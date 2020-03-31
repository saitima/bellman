use std::collections::HashMap;
use crate::{ConstraintSystem, LinearCombination, SynthesisError, Variable, Index, Circuit};
use crate::pairing::bls12_381::{Bls12, Fr};
use crate::pairing::Engine;
use crate::ff::{Field, PrimeField};
use crate::plonk::domains::Domain;
use crate::plonk::polynomials::{Polynomial, Values, Coefficients};
use crate::multicore::Worker;

pub struct Indexer<E: Engine>{
    domain_h: Domain<E::Fr>,
    domain_k: Domain<E::Fr>,
}
pub struct EncodedIndex<E: Engine>{
    domain_h: Domain<E::Fr>,
    domain_k: Domain<E::Fr>,
    a: EncodedMatrix<E>,
    b: EncodedMatrix<E>,
    c: EncodedMatrix<E>,
}

pub struct EncodedMatrix<E: Engine>{
    pub row_poly: Polynomial<E::Fr, Coefficients>,
    pub col_poly: Polynomial<E::Fr, Coefficients>,
    pub val_poly: Polynomial<E::Fr, Coefficients>,
    pub row_indexes: Vec<usize>,
    pub col_indexes: Vec<usize>,
}

// The output of I consists of the output of the lincheck indexer
// separately invoked on A, B, C. This produces nine univariate 
// polynomials {row_M , col_M , val_M } where M∈{A,B,C} over F of 
// degree less than |K| that can be used to compute the low-degree 
// extensions of A, B, C.
impl<E: Engine> Indexer<E>{
    
    pub fn encode(worker: &Worker, input: IndexerInput<E>) -> Result<EncodedIndex<E>, SynthesisError> {
        let domain_h = input.domain_h;
        let domain_k = input.domain_k;

        //The indexer I for the lincheck problem receives as input a field F, 
        // two subsets H and K of F, and a matrix M ∈ F^H×H with |K| ≥ ∥M∥.
        fn lincheck_indexer<E: Engine>(
            elements_of_domain_h: &[E::Fr],
            domain_k: Domain<E::Fr>,
            matrix: Vec<Vec<(usize, E::Fr)>>,
            worker: &Worker, 
            precomputed_bivariate_poly_with_same_inputs: &[E::Fr],
        ) -> Result<EncodedMatrix<E>, SynthesisError>{
            let mut row_evals : Vec<E::Fr> = Vec::new();
            let mut col_evals : Vec<E::Fr> = Vec::new();
            let mut val_evals : Vec<E::Fr> = Vec::new();
            let mut row_indexes : Vec<usize> = Vec::new();
            let mut col_indexes : Vec<usize> = Vec::new();

            let mut inverses = Vec::new();
            let factor = domain_k.size as usize / elements_of_domain_h.len();
            matrix.iter().enumerate().for_each(|(row_index, row)|{
                row.iter().for_each(|(col_index, coeff)|{
                    row_indexes.push(row_index);
                    col_indexes.push(*col_index);
                    // Given an n × n matrix M with rows/columns indexed by elements of H
                    row_evals.push(elements_of_domain_h[row_index]);
                    col_evals.push(elements_of_domain_h[*col_index]);
                    // val(κ) = coeff /(u_H(row(κ), row(κ))*u_H(col(κ), col(κ)))
                    // φ_K : K → [|K|] and φ−1(t_κ): [|K|] → K
                    // row(κ):  φ−1(t_κ) where t_κ is the row index of the φ(κ)-th nonzero entry in M;
                    let row_index_in_k = factor * row_index;
                    let col_index_in_k = factor * col_index;
                    let mut denom = precomputed_bivariate_poly_with_same_inputs[row_index_in_k].clone();
                    denom.mul_assign(&precomputed_bivariate_poly_with_same_inputs[col_index_in_k]);
                    inverses.push(denom);                    
                    val_evals.push(*coeff);            
                });
            }); 

            let mut val_poly_evals = Polynomial::from_values_unpadded(val_evals)?;
            let mut inverses_poly_evals = Polynomial::from_values_unpadded(inverses)?;
            inverses_poly_evals.batch_inversion(worker)?;
            val_poly_evals.mul_assign(worker, &inverses_poly_evals);

            // pad value polynomial
            val_poly_evals.pad_to_size(domain_k.size as usize)?;

            // pad arbitrary elements 
            (0..domain_k.size as usize -row_evals.len()).for_each(|_|{
                row_evals.push(E::Fr::one());
                col_evals.push(E::Fr::one());
            });

            let row_poly_evals = Polynomial::from_values(row_evals)?;
            let col_poly_evals = Polynomial::from_values(col_evals)?;
            let row_poly = row_poly_evals.ifft(worker);
            let col_poly = col_poly_evals.ifft(worker);
            let val_poly = val_poly_evals.ifft(worker);

            Ok(EncodedMatrix{
                row_poly,
                col_poly,
                val_poly,
                row_indexes,
                col_indexes,
            })
        }

        let elements_of_domain_h = domain_h.elements(worker);
        let precomputed_bivariate_poly_with_same_inputs = domain_h
        .evaluate_bivariate_polynomial_with_same_inputs(worker, &elements_of_domain_h);

        let a = lincheck_indexer(
            &elements_of_domain_h, 
            domain_k, 
            input.a_matrix, 
            worker, 
            &precomputed_bivariate_poly_with_same_inputs
        )?;

        let b = lincheck_indexer(
            &elements_of_domain_h, 
            domain_k, 
            input.b_matrix, 
            worker, 
            &precomputed_bivariate_poly_with_same_inputs
        )?;

        let c = lincheck_indexer(
            &elements_of_domain_h, 
            domain_k, 
            input.c_matrix, 
            worker, 
            &precomputed_bivariate_poly_with_same_inputs
        )?;

        Ok(EncodedIndex{
            domain_h,
            domain_k,
            a,
            b,
            c,
        })
    }
}

pub struct KeypairAssembly<E: Engine>{
    num_inputs: usize,
    num_aux: usize,
    num_constraints: usize,
    num_non_zeroes: usize,
    a: Vec<LinearCombination<E>>,
    b: Vec<LinearCombination<E>>,
    c: Vec<LinearCombination<E>>,
}

pub struct IndexerInput<E: Engine>{
    domain_h: Domain<E::Fr>,
    domain_k: Domain<E::Fr>,
    a_matrix: Vec<Vec<(usize, E::Fr)>>,
    b_matrix: Vec<Vec<(usize, E::Fr)>>,
    c_matrix: Vec<Vec<(usize, E::Fr)>>,
}

impl<E: Engine> KeypairAssembly<E>{
    pub fn new() -> Self{
        Self{
            num_inputs: 0,
            num_aux: 0,
            num_constraints: 0,
            num_non_zeroes: 0,
            a: Vec::new(),
            b: Vec::new(),
            c: Vec::new(),
        }
    }

    // number of non-zero elements should be greater or equal than 
    // number of constraints/variables (so we assume that R1CS 
    // matrixes are square that is always possible with padding 
    // and dummy variables with a constraint (a*1=a)
    pub fn pad_matrix(&mut self) -> Result<(), SynthesisError>{
        let diff = self.num_constraints - (self.num_inputs + self.num_aux);
        if diff > 0{
            (0..=diff).for_each(|_|{
                self.alloc(||"", ||{
                    Ok(E::Fr::one())
                }).unwrap();
            });

            self.a.resize(diff, LinearCombination::zero());
            self.b.resize(diff, LinearCombination::zero());
            self.c.resize(diff, LinearCombination::zero());
            // self.num_constraints = diff;
        }

        Ok(())
    }
    // 5.3.1 Offline phase: encoding the constraint system
    // The indexer I for R1CS receives as input a field F, 
    // two subsets H and K of F, and three matrices 
    // A, B, C ∈ F^H×H with |K| ≥ max{∥A∥, ∥B∥, ∥C∥}.
    pub fn prepare_inputs_for_indexer(self) -> Result<IndexerInput<E>, SynthesisError>{
        fn unwrap_and_arrange_indexes<E: Engine>(
            constraints: Vec<LinearCombination<E>>, 
            num_inputs: usize
        ) -> Vec<Vec<(usize, E::Fr)>>{            
            let mut matrix: Vec<Vec<(usize, E::Fr)>> = Vec::new();
            constraints.iter().for_each(|row|{
                let mut new_row: Vec<(usize, E::Fr)> = Vec::new();
                row.0.iter().for_each(|(variable, coeff)|{
                    let index = match variable{
                        Variable(Index::Input(index)) => *index,
                        Variable(Index::Aux(index)) => *index+num_inputs,
                    };
                    new_row.push((index, *coeff));
                });
                matrix.push(new_row);
            });
            matrix
        }

        let a_matrix = unwrap_and_arrange_indexes(self.a, self.num_inputs);
        let b_matrix = unwrap_and_arrange_indexes(self.b, self.num_inputs);
        let c_matrix = unwrap_and_arrange_indexes(self.c, self.num_inputs);

        // we do not need Domain struct, size of domains are enough.
        let domain_h_size = self.num_inputs + self.num_aux; // inputs + aux can be greater than num_constraints
        let domain_k_size = self.num_non_zeroes;

        let domain_h = Domain::<E::Fr>::new_for_size(domain_h_size as u64)?;
        let domain_k = Domain::<E::Fr>::new_for_size(domain_k_size as u64)?;
        

        Ok(IndexerInput{
            domain_h,
            domain_k,
            a_matrix,
            b_matrix,
            c_matrix,
        })
    }
}

impl<E: Engine> ConstraintSystem<E> for KeypairAssembly<E>{
    type Root = Self;

    fn alloc<F, A, AR>(
        &mut self, _: A, _: F
    ) -> Result<Variable, SynthesisError>{

        let index = self.num_aux;
        self.num_aux += 1;

        Ok(Variable(Index::Aux(index)))
    }

    fn alloc_input<F, A, AR>(
        &mut self, _: A, _: F
    ) -> Result<Variable, SynthesisError>{

        let index = self.num_inputs;
        self.num_inputs += 1;

        Ok(Variable(Index::Input(index)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where A: FnOnce() -> AR,
          AR: Into<String>,
          LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
          LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
          LC: FnOnce(LinearCombination<E>) -> LinearCombination<E> {
            // this function sum lc's elements with same variable index 
            // |lc| lc + a + b + c ... + b + c + ..
            // into 
            // |lc| lc + a + (b + b) + (c + c)
            // and then sorting by variable index
            fn sum_coeffs_of_same_variables_and_sort<E: Engine>(lc: LinearCombination<E>) -> LinearCombination<E>{
                let mut variables: Vec<Variable> = Vec::new();
                let mut coeffs : Vec<E::Fr> = Vec::new();
                lc.0.iter().for_each(|(variable, coeff)|{
                    if variables.contains(&variable){
                        let position = variables.iter().position(|e| e == variable).expect("should has index element");
                        coeffs[position].add_assign(&coeff);
                    }else{
                        variables.push(*variable);
                        coeffs.push(*coeff);
                    }                    
                }); 
                let mut new_lc = LinearCombination::zero();
                coeffs.iter().zip(variables.iter()).for_each(|(coeff, variable)|{
                    if !coeff.is_zero(){
                        new_lc.0.push((*variable, *coeff));
                    }
                });
                new_lc.0.sort_by(|(x,_),(y,_)| x.0.cmp(&y.0));
                new_lc
            }

            let lc_a = sum_coeffs_of_same_variables_and_sort(a(LinearCombination::zero()));
            let lc_b = sum_coeffs_of_same_variables_and_sort(b(LinearCombination::zero()));
            let lc_c = sum_coeffs_of_same_variables_and_sort(c(LinearCombination::zero()));
            
            // increase nnz in each enforcement step by max(a,b,c)
            let num_non_zeroes = *[lc_a.0.len(), lc_b.0.len(), lc_c.0.len()].iter().max().unwrap();
            self.a.push(lc_a);
            self.b.push(lc_b);
            self.c.push(lc_c);

            self.num_non_zeroes += num_non_zeroes;            
            self.num_constraints += 1;
          }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR { unimplemented!() }
    fn pop_namespace(&mut self) { unimplemented!() }
    fn get_root(&mut self) -> &mut Self::Root { unimplemented!() }        
}

struct TestCircuit<E: Engine>{
    x: Option<E::Fr>,
    y: Option<E::Fr>,
}

impl<E: Engine> Circuit<E> for TestCircuit<E>{
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        c: &mut CS
    ) -> Result<(), SynthesisError>{
        let x_var = c.alloc(|| "x",|| {
                if let Some(x_var) = self.x{
                    Ok(x_var)
                }else{
                    Err(SynthesisError::AssignmentMissing)
                }
            }
        )?;
        let y_var = c.alloc(|| "y", ||{
            if let Some(y_var) = self.y{
                Ok(y_var)
            }else{
                Err(SynthesisError::AssignmentMissing)
            }
        })?; 

        let z_var = c.alloc_input(|| "z", ||{        
            if let (Some(x_var), Some(y_var)) = (self.x, self.y){
                let mut z_var = x_var.clone();   
                z_var.add_assign(&y_var);
                Ok(z_var)
            }else{
                Err(SynthesisError::AssignmentMissing)
            }
        })?; 

        c.enforce(
            || "y + x + y + x + y = z + z + y",
            |lc| lc + y_var + x_var + y_var + x_var  + (E::Fr::zero(), y_var), // test with zero coeffs
            |lc| lc + CS::one()+ (E::Fr::zero(), y_var), // if allocated_input z is used here which one owns Input(0)?
            |lc| lc + z_var+ z_var +(E::Fr::zero(), y_var),
        );

        c.enforce(
            || "x+y = z",
            |lc| lc + x_var + y_var,
            |lc| lc + CS::one(),
            |lc| lc + z_var,
        );

        Ok(())
    }

}

#[test]
fn test_cs_consistency_after_enforcement(){
    let c = TestCircuit::<Bls12>{        
        x: None,
        y: None,
    };
    let kp = &mut KeypairAssembly::new();
    c.synthesize(kp).unwrap(); 

    assert_eq!(kp.num_aux, 2);
    assert_eq!(kp.num_inputs, 1);
    assert_eq!(kp.num_constraints, 2);
    assert_eq!(kp.num_non_zeroes, 4);

    let mut a_expected: Vec<Vec<(Variable, Fr)>> = Vec::new();
    let mut b_expected: Vec<Vec<(Variable, Fr)>> = Vec::new();
    let mut c_expected: Vec<Vec<(Variable, Fr)>> = Vec::new();
    a_expected.push(
        vec![
        (Variable(Index::Aux(0)), Fr::from_str("2").unwrap()),
        (Variable(Index::Aux(1)), Fr::from_str("2").unwrap())
        ]
    );
    a_expected.push(
        vec![
        (Variable(Index::Aux(0)), Fr::from_str("1").unwrap()),
        (Variable(Index::Aux(1)), Fr::from_str("1").unwrap())
        ]
    );
    
    b_expected.push(
        vec![
        (Variable(Index::Input(0)), Fr::from_str("1").unwrap()),
        ]
    );
    b_expected.push(
        vec![
        (Variable(Index::Input(0)), Fr::from_str("1").unwrap()),
        ]
    );
    
    c_expected.push(
        vec![
        (Variable(Index::Input(0)), Fr::from_str("2").unwrap()),
        ]
    );

    c_expected.push(
        vec![
        (Variable(Index::Input(0)), Fr::from_str("1").unwrap())
        ]
    );
    
    kp.a.iter().zip(a_expected.iter()).for_each(|(row, expected)|{
        row.0.iter().zip(expected.iter()).for_each(|((v1, c1), (v2, c2))|{
            assert_eq!(v1,v2);
            assert_eq!(c1, c2);
        });
    });
    kp.b.iter().zip(b_expected.iter()).for_each(|(row, expected)|{
        row.0.iter().zip(expected.iter()).for_each(|((v1, c1), (v2, c2))|{
            assert_eq!(v1,v2);
            assert_eq!(c1, c2);
        });
    });
    kp.c.iter().zip(c_expected.iter()).for_each(|(row, expected)|{
        row.0.iter().zip(expected.iter()).for_each(|((v1, c1), (v2, c2))|{
            assert_eq!(v1,v2);
            assert_eq!(c1, c2);
        });
    })
}