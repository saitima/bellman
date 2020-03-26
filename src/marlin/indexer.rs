use crate::marlin::helpers::*;
use crate::multicore::Worker;
use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::Engine;
use crate::plonk::domains::Domain;
use crate::plonk::polynomials::{Coefficients, Polynomial, Values};
use crate::{
    Circuit, ConstraintSystem, Index as VariableIndex, LinearCombination, SynthesisError, Variable,
};

pub fn construct_indexer<'a, E: Engine, C: Circuit<E>>(
    worker: &Worker,
    circuit: C,
) -> Result<Index<E>, SynthesisError> {
    let indexer = &mut Indexer::new();
    circuit.synthesize(indexer)?;
    indexer.make_matrix_square();
    indexer.index(worker)
}

#[derive(Debug, Clone)]
struct Indexer<E: Engine> {
    pub(crate) num_input_variables: usize,
    pub(crate) num_witness_variables: usize,
    pub(crate) num_constraints: usize,
    pub(crate) a: Vec<Vec<(E::Fr, VariableIndex)>>,
    pub(crate) b: Vec<Vec<(E::Fr, VariableIndex)>>,
    pub(crate) c: Vec<Vec<(E::Fr, VariableIndex)>>,
}

impl<'a, E: Engine> Indexer<E> {
    pub fn new() -> Self {
        Indexer {
            num_input_variables: 1,
            num_witness_variables: 0,
            num_constraints: 0,
            a: Vec::new(),
            b: Vec::new(),
            c: Vec::new(),
        }
    }

    pub fn index(&self, worker: &Worker) -> Result<Index<E>, SynthesisError> {
        let num_input_variables = self.num_input_variables;
        let num_witness_variables = self.num_witness_variables;
        let num_inputs = num_input_variables + num_witness_variables;
        let num_non_zero = self.num_non_zero();
        let num_constraints = self.num_constraints;
        assert_eq!(num_constraints, num_inputs, "matrix is not square");

        let domain_k = Domain::new_for_size(num_non_zero as u64)?;
        let domains = EvaluationDomains {
            h: Domain::new_for_size(num_constraints as u64)?,
            k: domain_k,
            x: Domain::new_for_size(self.num_input_variables as u64)?,
            b: Domain::new_for_size((6 * domain_k.size - 6) as u64)?,
        };

        let elements_of_domain_h = domains.h.elements(worker);
        let precomputed_bivariate_poly_with_same_inputs_on_domain_h = domains
            .h
            .evaluate_bivariate_polynomial_with_same_inputs(worker, &elements_of_domain_h);
        let a_matrix = Matrix::new(
            worker,
            self.a.clone(),
            &domains,
            num_input_variables,
            &elements_of_domain_h,
            &precomputed_bivariate_poly_with_same_inputs_on_domain_h,
        )?;
        let b_matrix = Matrix::new(
            worker,
            self.b.clone(),
            &domains,
            num_input_variables,
            &elements_of_domain_h,
            &precomputed_bivariate_poly_with_same_inputs_on_domain_h,
        )?;
        let c_matrix = Matrix::new(
            worker,
            self.c.clone(),
            &domains,
            num_input_variables,
            &elements_of_domain_h,
            &precomputed_bivariate_poly_with_same_inputs_on_domain_h,
        )?;
        let precomputed_bivariate_poly_with_same_inputs_on_domain_h =
            Polynomial::from_values(precomputed_bivariate_poly_with_same_inputs_on_domain_h)?;

        Ok(Index {
            a_index: a_matrix.encode(worker, &elements_of_domain_h)?,
            b_index: b_matrix.encode(worker, &elements_of_domain_h)?,
            c_index: c_matrix.encode(worker, &elements_of_domain_h)?,
            domains,
            elements_of_domain_h,
            precomputed_bivariate_poly_with_same_inputs_on_domain_h,
        })
    }
}

impl<E: Engine> ConstraintSystem<E> for Indexer<E> {
    type Root = Self;

    #[inline]
    fn alloc<FN, A, AR>(&mut self, _: A, _: FN) -> Result<Variable, SynthesisError>
    where
        FN: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.num_witness_variables;
        self.num_witness_variables += 1;

        Ok(Variable(VariableIndex::Aux(index)))
    }

    fn alloc_input<FN, A, AR>(&mut self, _: A, _: FN) -> Result<Variable, SynthesisError>
    where
        FN: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.num_input_variables;
        self.num_input_variables += 1;

        Ok(Variable(VariableIndex::Input(index)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        self.a.push(Self::make_row(&a(LinearCombination::zero())));
        self.b.push(Self::make_row(&b(LinearCombination::zero())));
        self.c.push(Self::make_row(&c(LinearCombination::zero())));

        self.num_constraints += 1;
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self) {}

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

#[derive(Debug, Clone)]
pub struct Matrix<E: Engine> {
    pub matrix: Vec<Vec<(usize, E::Fr)>>,
    pub row: Vec<E::Fr>,
    pub col: Vec<E::Fr>,
    pub val: Vec<E::Fr>,
}
#[derive(Debug, Clone)]
pub struct MatrixPolynomialCoeffs<E: Engine> {
    pub row: Polynomial<E::Fr, Coefficients>,
    pub col: Polynomial<E::Fr, Coefficients>,
    pub val: Polynomial<E::Fr, Coefficients>,
}
#[derive(Debug, Copy, Clone)]
pub struct EvaluationDomains<E: Engine> {
    pub h: Domain<E::Fr>,
    pub k: Domain<E::Fr>,
    pub b: Domain<E::Fr>,
    pub x: Domain<E::Fr>,
}

#[derive(Debug, Clone)]
pub struct MatrixEncoding<E: Engine> {
    pub matrix: Matrix<E>,
    pub row_poly: Polynomial<E::Fr, Coefficients>,
    pub col_poly: Polynomial<E::Fr, Coefficients>,
    pub val_poly: Polynomial<E::Fr, Coefficients>,
    pub val_evals_on_k: Vec<E::Fr>,
    pub row_indexes_on_domain_h: Vec<usize>,
    pub col_indexes_on_domain_h: Vec<usize>,
}

#[derive(Clone)]
pub struct Index<E: Engine> {
    pub domains: EvaluationDomains<E>,
    pub a_index: MatrixEncoding<E>,
    pub b_index: MatrixEncoding<E>,
    pub c_index: MatrixEncoding<E>,
    pub elements_of_domain_h: Vec<E::Fr>,
    pub precomputed_bivariate_poly_with_same_inputs_on_domain_h: Polynomial<E::Fr, Values>,
}

impl<E: Engine> Index<E> {
    pub fn get_matrix_encoding(&self, which: MatrixType) -> MatrixEncoding<E> {
        match which {
            MatrixType::A => self.a_index.clone(),
            MatrixType::B => self.b_index.clone(),
            MatrixType::C => self.c_index.clone(),
        }
    }
}

pub enum MatrixType {
    A,
    B,
    C,
}

impl<E: Engine> Matrix<E> {
    pub fn new(
        worker: &Worker,
        data: Vec<Vec<(E::Fr, VariableIndex)>>,
        domains: &EvaluationDomains<E>,
        num_input_variables: usize,
        elements_of_domain_h: &[E::Fr],
        precomputed_bivariate_polynomial: &[E::Fr],
    ) -> Result<Self, SynthesisError> {
        let mut matrix = Self {
            matrix: Vec::new(),
            col: Vec::new(),
            row: Vec::new(),
            val: Vec::new(),
        };
        let mut inverses = Vec::new();
        let ratio = (domains.h.size / domains.x.size) as usize;
        data.iter().enumerate().for_each(|(row_index, row)| {
            let mut new_row: Vec<(usize, E::Fr)> = Vec::new();
            let mut sorted_row = row.clone();
            sorted_row.sort_by(|(_, a), (_, b)| a.cmp(b));
            sorted_row.iter().for_each(|(val, col)| {
                let mut col_index = match col {
                    VariableIndex::Input(i) => *i,
                    VariableIndex::Aux(i) => num_input_variables + (*i), // witness
                };
                new_row.push((col_index, *val));
                // find actual index of element in output domain
                col_index = {
                    if col_index < domains.x.size as usize {
                        col_index * ratio
                    } else {
                        let i = col_index - domains.x.size as usize;
                        let x = ratio - 1;
                        i + (i / x) + 1
                    }
                };
                let row_k = elements_of_domain_h[row_index];
                let col_k = elements_of_domain_h[col_index];
                matrix.row.push(row_k);
                matrix.col.push(col_k);

                // val(κ)/(u_H(row(κ), row(κ))*u_H(col(κ), col(κ)))
                let mut denominator = precomputed_bivariate_polynomial[row_index].clone();
                denominator.mul_assign(&precomputed_bivariate_polynomial[col_index]);
                let numerator = val.clone();
                matrix.val.push(numerator);
                inverses.push(denominator);
            });
            matrix.matrix.push(new_row.clone()); // raw matrix
        });

        let mut inverses = Polynomial::from_values_unpadded(inverses)?;
        inverses.batch_inversion(worker)?;
        matrix
            .val
            .iter_mut()
            .zip(inverses.as_ref().iter())
            .for_each(|(val, inv)| {
                val.mul_assign(inv);
            });

        (0..((domains.k.size as usize) - matrix.val.len())).for_each(|_| {
            matrix.row.push(elements_of_domain_h[0]); // arbitrary elem
            matrix.col.push(elements_of_domain_h[0]); // arbitrary elem
            matrix.val.push(E::Fr::zero()); // one
        });
        Ok(matrix)
    }

    pub fn linear_combination(&self, z: &[E::Fr]) -> Vec<E::Fr> {
        let mut result = Vec::new();
        z.iter().zip(self.matrix.iter()).for_each(|(_, row)| {
            let mut acc = E::Fr::zero();
            row.iter().for_each(|(col, coeff)| {
                let mut tmp = coeff.clone();
                tmp.mul_assign(&z[*col]);
                acc.add_assign(&tmp);
            });
            result.push(acc);
        });
        result
    }

    pub fn encode(
        &self,
        worker: &Worker,
        elements_of_domain_h: &[E::Fr],
    ) -> Result<MatrixEncoding<E>, SynthesisError> {
        // evals on domain k
        let row_evals_on_k = Polynomial::from_values(self.row.to_vec())?;
        let col_evals_on_k = Polynomial::from_values(self.col.to_vec())?;
        let val_evals_on_k = Polynomial::from_values(self.val.to_vec())?;
        let mut row_indexes_on_domain_h = Vec::new();
        let mut col_indexes_on_domain_h = Vec::new();

        row_evals_on_k
            .as_ref()
            .iter()
            .zip(col_evals_on_k.as_ref().iter())
            .for_each(|(row, col)| {
                elements_of_domain_h
                    .iter()
                    .enumerate()
                    .for_each(|(i, elem)| {
                        if row == elem {
                            row_indexes_on_domain_h.push(i);
                        }
                        if col == elem {
                            col_indexes_on_domain_h.push(i);
                        }
                    });
            });

        // univariate polynomials
        let row_poly = row_evals_on_k.ifft(worker);
        let col_poly = col_evals_on_k.ifft(worker);
        let val_poly = val_evals_on_k.clone().ifft(worker);
        let val_evals_on_k = val_evals_on_k.into_coeffs();

        Ok(MatrixEncoding {
            matrix: self.clone(),
            row_poly,
            col_poly,
            val_poly,
            row_indexes_on_domain_h,
            col_indexes_on_domain_h,
            val_evals_on_k,
        })
    }
}

impl<E: Engine> Indexer<E> {
    #[inline]
    fn make_row(l: &LinearCombination<E>) -> Vec<(E::Fr, VariableIndex)> {
        l.as_ref()
            .iter()
            .map(|(var, coeff)| (*coeff, var.get_unchecked()))
            .collect()
    }

    pub fn num_non_zero(&self) -> usize {
        let a_density = self.a.iter().map(|r| r.len()).sum();
        let b_density = self.b.iter().map(|r| r.len()).sum();
        let c_density = self.c.iter().map(|r| r.len()).sum();

        let max = *[a_density, b_density, c_density]
            .iter()
            .max()
            .expect("not empty");

        max
    }
    // r: number of constraints = number of rows
    // c: number of non-zero = number of cols
    // dim = abs(r-c)
    pub fn make_matrix_square(&mut self) {
        let num_variables = self.num_input_variables + self.num_witness_variables; // alloc & alloc_input
        let num_non_zero = self.num_non_zero(); // variables by enforcing
        let dim = std::cmp::max(num_variables, self.num_constraints);
        let diff = self.num_constraints as isize - num_variables as isize;
        if diff != 0 {
            self.pad_variables(diff as isize);
        }
        assert_eq!(
            self.num_input_variables + self.num_witness_variables,
            self.num_constraints,
            "padding failed"
        );
        assert_eq!(
            self.num_input_variables + self.num_witness_variables,
            dim,
            "padding does not result in expected matrix size!"
        );
        assert_eq!(
            self.num_non_zero(),
            num_non_zero,
            "padding changed matrix density"
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
