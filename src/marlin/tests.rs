use crate::{SynthesisError};
use crate::pairing::{Engine};
use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::bls12_381::{Bls12, Fr, Fq, FqRepr};
use crate::{Circuit, ConstraintSystem};
use rand::{Rand, thread_rng, ThreadRng};

#[derive(Copy, Clone)]
pub struct DummyCircuit<E: Engine>{
    a: Option<E::Fr>,
    b: Option<E::Fr>,
    num_constraints: usize,
    num_variables: usize,
}

impl<E: Engine> Circuit<E> for DummyCircuit<E>{
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.alloc_input(
            || "c",
            || {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let  b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
                a.mul_assign(&b);
                Ok(a)
            }            
        )?;
        //we already have 1 pre-defiend  and 2 (which is a,b) so we need reduced
        for i in 0..(self.num_variables-3){
            let _ = cs.alloc(|| format!("var {}", i), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for i in 0..self.num_constraints{
            cs.enforce(
                || format!("constraint {}", i),
                |lc| lc + a,
                |lc| lc + b,
                |lc| lc + c,
            )
        }

        Ok(())
    }
}


// y = x^3 + x + 5 where i know some x which makes y=35
// https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649
#[derive(Copy, Clone)]
pub struct DemoCircuit<E: Engine>{
    pub x: Option<E::Fr>,
}

impl <E: Engine>Circuit<E> for DemoCircuit<E>{

    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>{
        // flattened form
        // sym1=x*x
        // y=sym1*x
        // sym2=y+x
        // out=sym2+5

        let x_val = self.x;
        let x = cs.alloc(|| "allocation of x", || {
            x_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let sym1_val = x_val.map(|x| {
            let mut x = x.clone();
            x.square();
            x
        });

        let sym1 = cs.alloc(|| "allocation of sym1", || {
            sym1_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        // x*x==sym1
        cs.enforce(
            || "sym1=x*x",
            |lc| lc + x,
            |lc| lc + x, 
            |lc| lc + sym1
        );

        let y_val = sym1_val.map(|sym1|{
            let mut sym1 = sym1.clone();
            sym1.mul_assign(&x_val.unwrap());
            sym1
        });

        let y = cs.alloc(|| "allocation of y", || {
            y_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        // sym1*x==y
        cs.enforce(
            || "y=sym1*x", 
            |lc| lc + sym1, 
            |lc| lc + x, 
            |lc| lc + y
        );

        let sym2_val = y_val.map(|sym2| {
            let mut sym2 = sym2.clone();
            sym2.add_assign(&x_val.unwrap());
            sym2
        });

        let sym2 = cs.alloc(|| "allocation of sym2", || {
            sym2_val.ok_or(SynthesisError::AssignmentMissing)            
        })?;        
        // y+x==sym2
        cs.enforce(
            || "sym2=y+x",
            |lc| lc + y + x,
            |lc| lc + CS::one(),
            |lc| lc + sym2
        );

        let five = E::Fr::from_str("5").unwrap();
        let out_val = sym2_val.map(|out|{
            let mut out = out.clone();
            out.add_assign(&five);
            out
        });

        let out = cs.alloc_input(|| "out", || {
            out_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        // out=sym2+5
        cs.enforce(
            || "out=sym2+5", 
            |lc| lc + sym2 + (five, CS::one()), 
            |lc| lc + CS::one() , 
            |lc| lc + out
        );

        Ok(())
    }
}


#[test]
fn test_prover_verifier(){
    use crate::marlin::indexer::{construct_indexer};
    use crate::marlin::prover::{create_proof};
    use crate::marlin::verifier::{verify_proof};
    use crate::multicore::Worker;
    use crate::rand::ThreadRng;

    let rng = &mut thread_rng();
    let worker = &Worker::new();

    let a = Fr::from_str(&3.to_string()).unwrap();
    let b = Fr::from_str(&4.to_string()).unwrap();
    
    

    let num_constraints = 5;
    let num_variables = 5;
    let circuit = DummyCircuit::<Bls12>{ a: Some(a), b: Some(b), num_constraints, num_variables };

    let index = construct_indexer::<Bls12, DummyCircuit<Bls12>>(worker, circuit.clone()).unwrap();

    let proof = create_proof::<Bls12, DummyCircuit<Bls12>, ThreadRng>(worker, &index, circuit, rng).unwrap();

    let mut public_input = a.clone();    
    public_input.mul_assign(&b);

    let verified = verify_proof::<Bls12>(worker, &index, &proof, &[public_input]).unwrap();
    
    assert!(verified);
}

#[test]
fn test_custom_circuit(){
    use crate::marlin::indexer::construct_indexer;
    use crate::marlin::prover::create_proof;
    use crate::marlin::verifier::verify_proof;
    use crate::multicore::Worker;
    use crate::rand::ThreadRng;

    let rng = &mut thread_rng();
    let worker = &Worker::new();

    let circuit = DemoCircuit::<Bls12>{
        x: None,
    };

    let index = construct_indexer::<Bls12, DemoCircuit<Bls12>>(worker, circuit.clone()).unwrap();
    
    let x = Fr::from_str("3").unwrap();
    let circuit = DemoCircuit::<Bls12>{
        x: Some(x),
    };

    let proof = create_proof::<Bls12, DemoCircuit<Bls12>, ThreadRng>(worker, &index, circuit, rng).unwrap();

    let public_input = Fr::from_str("35").unwrap();

    let verified = verify_proof::<Bls12>(worker, &index, &proof, &[public_input]).unwrap();
    
    assert!(verified);
}



#[test]
fn marlin_divide_vanish(){
    use crate::multicore::Worker;
    use crate::plonk::domains::Domain;
    use crate::plonk::polynomials::{Polynomial, Values, Coefficients};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use crate::pairing::Engine;
    use crate::pairing::ff::{Field, PrimeField};
    let zero = Fr::zero();
    let one = Fr::one();
    let mut neg_one = one.clone();
    neg_one.negate();    
    let x_coeffs = vec![one, zero, one, one , one ];
    let px = Polynomial::<Fr, Coefficients>::from_coeffs(x_coeffs).unwrap();
    let domain = Domain::new_for_size(2).unwrap();    
    let (qx, rx ) = px.divide_by_vanishing_poly(domain).unwrap();
    println!("quotient q(x)");
    qx.into_coeffs().iter().for_each(|e| println!("{}", e));
    println!("remainder r(x)");
    rx.into_coeffs().iter().for_each(|e| println!("{}", e));
}

#[test]
fn marlin_multiply_vanish(){
    use crate::multicore::Worker;
    use crate::plonk::domains::Domain;
    use crate::plonk::polynomials::{Polynomial, Values, Coefficients};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use crate::pairing::Engine;
    use crate::pairing::ff::{Field, PrimeField};
    let worker = &Worker::new();
    let zero = Fr::zero();
    let one = Fr::one();
    let mut neg_one = one.clone();
    neg_one.negate();    
    let x_coeffs = vec![one, zero, one, one , one ];
    let px = Polynomial::<Fr, Coefficients>::from_coeffs(x_coeffs).unwrap();
    let domain = Domain::new_for_size(2).unwrap();    
    let v = domain.get_vanishing_polynomial().unwrap();
    v.clone().into_coeffs().iter().for_each(|e| println!("{}",e));
    println!();
    let v_evals = v.lde(worker, 2).unwrap();

    let mut result = px.clone().fft(worker).clone();
    result.mul_assign(worker, &v_evals);
    result.clone().ifft(worker).into_coeffs().iter().for_each(|e| println!("{}", e));

    let result2 = px.mul_by_vanishing_poly(domain);
    assert_eq!(result.ifft(worker), result2);
}

#[test]
fn test_poly_eval(){
    use crate::multicore::Worker;
    use crate::plonk::domains::Domain;
    use crate::plonk::polynomials::{Polynomial, Values, Coefficients};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use crate::pairing::Engine;
    use crate::pairing::ff::{Field, PrimeField};
    let worker = &Worker::new();
    let one = Fr::one();
    let mut neg_one = one.clone();
    neg_one.negate();
    let mut two = one.clone();
    two.double();
    // make two polynomials of degree two
    let coeffs_a = vec![neg_one, one, two];
    let coeffs_b = vec![two, neg_one, one];
    let poly_a = Polynomial::<Fr, Coefficients>::from_coeffs(coeffs_a.clone()).unwrap();
    let poly_b = Polynomial::<Fr, Coefficients>::from_coeffs(coeffs_b.clone()).unwrap();
    assert_ne!(poly_a.size(),3);
    assert_eq!(poly_a.size(),4);

    // evaluate at degree 8 domain
    let domain = Domain::new_for_size((2*coeffs_a.len()) as u64).unwrap();
    let evals_a_on_domain: Vec<Fr> = domain.elements(worker).iter().map(|e|{
        poly_a.evaluate_at(worker, *e)
    }).collect();
    let evals_b_on_domain: Vec<Fr> = domain.elements(worker).iter().map(|e|{
        poly_b.evaluate_at(worker, *e)
    }).collect();
    assert_eq!(evals_a_on_domain.len(), 8);
    assert_eq!(evals_b_on_domain.len(), 8);

    // make two eval polynomial from evaluations
    let eval_a = Polynomial::<Fr, Values>::from_values(evals_a_on_domain).unwrap();
    let eval_b = Polynomial::<Fr, Values>::from_values(evals_b_on_domain).unwrap();

    // make two eval polynomials via lde
    let factor = 2; // (output_domain / input_domain)
    let evals_a_on_domain_via_lde = poly_a.clone().lde(worker, factor).unwrap();
    let evals_b_on_domain_via_lde = poly_b.clone().lde(worker, factor).unwrap();
    
    assert_eq!(eval_a, evals_a_on_domain_via_lde);
    assert_eq!(eval_b, evals_b_on_domain_via_lde);

    // make two eval polynomials via fft
    let mut poly_a_resized = poly_a.clone();
    poly_a_resized.pad_to_size(8).unwrap();
    let mut poly_b_resized = poly_b.clone();
    poly_b_resized.pad_to_size(8).unwrap();
    let evals_a_on_domain_via_fft = poly_a_resized.fft(worker);
    let evals_b_on_domain_via_fft = poly_b_resized.fft(worker);
    
    assert_eq!(eval_a, evals_a_on_domain_via_fft);
    assert_eq!(eval_b, evals_b_on_domain_via_fft);

    // multiply two polynomials
    let mut eval_result = eval_a.clone();
    eval_result.mul_assign(worker, &eval_b);
    
    // convert back to monomial basis
    let poly_result = eval_result.ifft(worker);    
    assert_eq!(poly_result.size(), 8);

    // expected poly is 2x^4-x^3+2x^2+3x-2
    let mut neg_two = neg_one.clone();
    neg_two.double();
    let mut three = two.clone();
    three.add_assign(&one);
    let expected_coeffs = vec![neg_two, three, two, neg_one, two];
    let expected_poly =  Polynomial::<Fr, Coefficients>::from_coeffs(expected_coeffs).unwrap();
    assert_eq!(poly_result, expected_poly);
}

#[test]
fn test_batch_inversion(){
    use crate::multicore::Worker;
    use crate::plonk::domains::Domain;
    use crate::plonk::polynomials::{Polynomial, Values, Coefficients};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use crate::pairing::Engine;
    use crate::pairing::ff::{Field, PrimeField};
    let worker = &Worker::new();

    let one = Fr::one();
    let mut neg_one = one.clone();
    neg_one.negate();
    let mut two = one.clone();
    two.double();
    // p(x) = x^3 + 2*x^2 + x - 1
    let mut px_evals = vec![neg_one.clone(), one.clone(), two.clone(), one.clone()];
    let mut px = Polynomial::<Fr, Values>::from_values(px_evals.clone()).unwrap();
    px.batch_inversion(worker).unwrap();
    px_evals.iter_mut().for_each(|e| *e = e.inverse().unwrap());
    assert_eq!(px_evals, px.clone().into_coeffs());
}

#[test]
fn test_coset_poly(){
    use crate::multicore::Worker;
    use crate::plonk::domains::Domain;
    use crate::plonk::polynomials::{Polynomial, Values, Coefficients};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use crate::pairing::Engine;
    use crate::pairing::ff::{Field, PrimeField};
    let worker = &Worker::new();
    let zero = Fr::zero();
    let one = Fr::one();
    let mut neg_one = one.clone();
    neg_one.negate();
    let mut two = one.clone();
    two.double();
    let mut three = two.clone();
    three.add_assign(&one);
    // p(x) = x^3 + 2*x^2 + x - 1
    let px_coeffs = vec![neg_one.clone(), one.clone(), two.clone(), one.clone()];
    let px = Polynomial::<Fr, Coefficients>::from_coeffs(px_coeffs.clone()).unwrap();
    // q(x) = -x^3 + x^2 + 2x + 1
    let qx_coeffs = vec![one.clone(), two.clone(), one.clone(), neg_one.clone()];
    let qx = Polynomial::<Fr, Coefficients>::from_coeffs(qx_coeffs.clone()).unwrap();

    let factor = 4;
    let c1 = px.coset_lde(worker, factor).unwrap();
    let c2 = qx.coset_lde(worker, factor).unwrap();
    // let c1 = px.lde(worker, factor).unwrap();
    // let c2 = qx.lde(worker, factor).unwrap();

    let mut result = c1.clone();
    result.add_assign(worker, &c2);
    let mut tx = result.ifft(worker);
    
    // tx = p(x) + q(x) = 
    // p(x) = x^3 + 2*x^2 + x - 1
    // q(x) = -x^3 + x^2 + 2x + 1
    // t(x) = 0x^3 + 3x^2 + 3x + 0

    let expected_coefss = vec![zero.clone(), three.clone(), three.clone(), zero.clone()];
    let expected = Polynomial::<Fr, Coefficients>::from_coeffs(expected_coefss).unwrap();
    let tx_size = tx.clone().size();
    let ex_size = expected.clone().size();
    let degree = *[tx_size, ex_size].iter().min().unwrap();
    tx.trim_to_degree(degree).unwrap();
    assert_eq!(tx, expected);
}

#[test]
fn test_worker_scop(){
    use crate::multicore::Worker;

    let worker = &Worker::new();

    let mut batch_data_one = vec![0; 50];
    // let batch_data_one: Vec<usize> = Vec::with_capacity(50);
    // let batch_data_two = Vec::with_capacity(50);

    worker.scope(batch_data_one.len(), |scope, chunk_size|{ // chunk_size calculated by number of cpu 
        for (chunk_id, chunk) in batch_data_one.chunks_mut(chunk_size).enumerate(){
            scope.spawn(move |_|{
                for (i, elem) in chunk.iter_mut().enumerate(){
                    println!("chunk id {} elem: {}", chunk_id, i);
                    *elem = i * 4;
                }
            });
        }
    });

    println!("{:?}", batch_data_one);
}