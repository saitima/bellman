use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::Engine;

use crate::plonk::domains::*;
use crate::plonk::polynomials::*;
use crate::worker::Worker;
use crate::SynthesisError;

use std::marker::PhantomData;

use super::cs::*;
use super::keys::{PlookupProof, Proof, SetupPolynomials, SetupPolynomialsPrecomputations};

use crate::source::{DensityTracker, DensityTrackerersChain};

use super::utils::*;
use crate::kate_commitment::*;

use crate::plonk::commitments::transcript::*;
use crate::plonk::fft::cooley_tukey_ntt::*;

use super::lookup_table::{LookupTable, RangeTable, TableType};
use super::LDE_FACTOR;

use super::multiset::MultiSet;

// #[derive(Debug, Clone)]
pub struct ProverAssembly<'a, E: Engine, P: PlonkConstraintSystemParams<E>> {
    m: usize,
    n: usize,
    num_inputs: usize,
    num_aux: usize,
    num_standard_lookups: usize,
    num_range_lookups: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    wire_assignments: Vec<Vec<E::Fr>>,

    inputs_map: Vec<usize>,
    dummy_var: Variable,

    is_finalized: bool,

    lookup_tables: &'a mut [Box<dyn LookupTable<E::Fr>>], // TODO: make optional
    // lookup_tables: Vec<Box<dyn LookupTable<E::Fr>>>, // TODO: make optional
    // lookup_tables: Option<&'a mut [Box<dyn LookupTable<E::Fr>>]>, // TODO: make optional
    is_table_initialized: bool,

    _marker: std::marker::PhantomData<P>,
}

impl<'a, E: Engine, P: PlonkConstraintSystemParams<E>> ConstraintSystem<E, P>
    for ProverAssembly<'a, E, P>
{
    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let value = value()?;

        self.num_inputs += 1;
        let index = self.num_inputs;
        self.input_assingments.push(value);

        let input_var = Variable(Index::Input(index));

        // there is an implicit gate to constraint the input
        // and it's handled during the proving
        self.n += 1;

        Ok(input_var)
    }

    // allocate an abstract gate
    fn new_gate(
        &mut self,
        variables: P::StateVariables,
        _this_step_coeffs: P::ThisTraceStepCoefficients,
        _next_step_coeffs: P::NextTraceStepCoefficients,
    ) -> Result<(), SynthesisError> {
        for (idx, &v) in variables.as_ref().iter().enumerate() {
            let val = self.get_value(v)?;
            self.wire_assignments[idx].push(val);
        }
        self.n += 1;

        Ok(())
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Aux(0)) => {
                E::Fr::zero()
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(0)) => {
                unreachable!();
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(input)) => self.input_assingments[input - 1],
            Variable(Index::Aux(aux)) => self.aux_assingments[aux - 1],
        };

        Ok(value)
    }

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }

    fn read_from_table(
        &mut self,
        table_type: TableType,
        a: Variable,
        b: Variable,
    ) -> Result<Variable, SynthesisError> {
        assert!(self.is_table_initialized);

        // TODO: this is ugly implementation, make better
        for (i, lookup_table) in self.lookup_tables.iter().enumerate() {
            let table_id = self.lookup_tables[i].lookup_table_type_as_fe();

            match (table_type.clone(), lookup_table.lookup_type()) {
                (TableType::XOR, TableType::XOR) | (TableType::AND, TableType::AND) => {
                    let a_val = self.get_value(a)?;
                    let b_val = self.get_value(b)?;
                    let c_val = lookup_table.query(a_val, b_val).expect("should has value");

                    let c = self.alloc(|| Ok(c_val))?;

                    self.wire_assignments[0].push(a_val);
                    self.wire_assignments[1].push(b_val);
                    self.wire_assignments[2].push(c_val);
                    self.wire_assignments[3].push(E::Fr::zero());

                    // store them also in lookup table object

                    self.lookup_tables[i]
                        .add_gate(MultiSet::from_vec([a_val, b_val, c_val, table_id]));

                    self.n += 1;
                    self.num_standard_lookups += 1;
                    return Ok(c);
                }
                (TableType::Range, TableType::Range) => {
                    // we use single-value lookup for now.
                    let a_val = self.get_value(a)?;

                    let c_val = lookup_table
                        .query(a_val, E::Fr::zero())
                        .expect("should has value in range");

                    let c = self.alloc(|| Ok(c_val))?;

                    self.wire_assignments[0].push(a_val);
                    self.wire_assignments[1].push(E::Fr::zero());
                    self.wire_assignments[2].push(E::Fr::zero());
                    self.wire_assignments[3].push(E::Fr::zero());

                    // store them also in lookup table object
                    self.lookup_tables[i].add_gate(MultiSet::from_vec([
                        a_val,
                        E::Fr::zero(),
                        E::Fr::zero(),
                        table_id,
                    ]));

                    self.n += 1;
                    self.num_range_lookups += 1;

                    return Ok(c);
                }
                _ => (),
            };
        }

        return Err(SynthesisError::Unsatisfiable);
    }
}

impl<'a, E: Engine, P: PlonkConstraintSystemParams<E>> ProverAssembly<'a, E, P> {
    pub fn new() -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,
            num_standard_lookups: 0,
            num_range_lookups: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            wire_assignments: vec![vec![]; P::STATE_WIDTH],

            // aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],
            inputs_map: vec![],
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            // lookup_tables: None,
            lookup_tables: &mut [],
            is_table_initialized: false,

            _marker: std::marker::PhantomData,
        };

        tmp
    }

    pub fn new_with_size_hints(num_inputs: usize, num_aux: usize) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,
            num_standard_lookups: 0,
            num_range_lookups: 0,

            input_assingments: Vec::with_capacity(num_inputs),
            aux_assingments: Vec::with_capacity(num_aux),

            wire_assignments: vec![Vec::with_capacity(num_inputs + num_aux); P::STATE_WIDTH],

            // aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],
            inputs_map: Vec::with_capacity(num_inputs),
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            // lookup_tables: None,
            lookup_tables: &mut [],
            is_table_initialized: false,

            _marker: std::marker::PhantomData,
        };

        tmp
    }

    // pub fn new_with_lookup_tables(lookup_tables: Vec<Box<dyn LookupTable<E::Fr>>>) -> Self {
    pub fn new_with_lookup_tables(lookup_tables: &'a mut [Box<dyn LookupTable<E::Fr>>]) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,
            num_inputs: 0,
            num_aux: 0,
            num_standard_lookups: 0,
            num_range_lookups: 0,
            input_assingments: vec![],
            aux_assingments: vec![],
            wire_assignments: vec![vec![]; P::STATE_WIDTH],
            inputs_map: vec![],
            dummy_var: Variable(Index::Aux(0)),
            is_finalized: false,
            // lookup_tables: Some(lookup_tables),
            lookup_tables: lookup_tables,
            is_table_initialized: true,

            _marker: std::marker::PhantomData,
        };

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn num_gates(&self) -> usize {
        self.n
    }

    pub fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }

        let n = if self.is_table_initialized {
            // number of standard lookup gates

            let mut standard_table_size = 0;
            let mut range_table_size = 0;

            for table in self.lookup_tables.iter() {
                match table.lookup_type() {
                    TableType::Range => range_table_size += table.size(),
                    _ => standard_table_size += table.size(),
                }
            }

            let num_standard_lookup_gates = self.num_standard_lookups;
            let num_range_lookup_gates = self.num_range_lookups;

            let filled_gates = self.n + self.num_inputs;

            let n = filled_gates
                .max(standard_table_size + num_standard_lookup_gates)
                .max(range_table_size + num_range_lookup_gates);
            n
        } else {
            self.n
        };

        if (n + 1).is_power_of_two() {
            self.is_finalized = true;
            return;
        }

        for _ in (self.n + 1)..(n + 1).next_power_of_two() {
            let variables = P::StateVariables::from_variables(&vec![self.get_dummy_variable(); 4]);
            self.new_gate(
                variables,
                P::ThisTraceStepCoefficients::empty(),
                P::NextTraceStepCoefficients::empty(),
            )
            .unwrap(); // TODO: change func signature to handle Result?
        }

        //TODO: d <= n then pad table with n-d +1 times by last element of table

        self.is_finalized = true;
    }

    pub fn get_witness_polynomials(&self) -> Result<Vec<Vec<E::Fr>>, SynthesisError> {
        assert!(self.is_finalized);

        let mut full_assignments =
            vec![Vec::with_capacity((self.n + 1).next_power_of_two()); self.wire_assignments.len()];

        for inp in self.input_assingments.clone().into_iter() {
            // inputs will always go into A wire
            full_assignments[0].push(inp);
            for i in 1..full_assignments.len() {
                full_assignments[i].push(E::Fr::zero());
            }
        }

        for (idx, aux) in self.wire_assignments.clone().into_iter().enumerate() {
            full_assignments[idx].extend(aux);
            full_assignments[idx].resize((self.n + 1).next_power_of_two() - 1, E::Fr::zero());
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), (self.n + 1).next_power_of_two() - 1);
        }

        Ok(full_assignments)
    }
}
#[derive(Clone)]
struct LookupResult<E: Engine> {
    challenge: E::Fr,

    quotient: Polynomial<E::Fr, Values>,
    z_in_monomial: Polynomial<E::Fr, Coefficients>,
    s_in_monomial: Polynomial<E::Fr, Coefficients>,
    witness_in_monomial: Polynomial<E::Fr, Coefficients>,
    table_values_in_monomial: Polynomial<E::Fr, Coefficients>,
    tables_in_monomial: Vec<Polynomial<E::Fr, Coefficients>>,

    s_commitment: E::G1Affine,
    grand_product_commitment: E::G1Affine,
}

// later we can alias traits
// pub trait PlonkCsWidth3WithNextStep<E: Engine> = ConstraintSystem<E, PlonkCsWidth3WithNextStepParams>;

pub type ProverAssembly3WithNextStep<'a, E> =
    ProverAssembly<'a, E, PlonkCsWidth3WithNextStepParams>;
pub type ProverAssembly4WithNextStep<'a, E> =
    ProverAssembly<'a, E, PlonkCsWidth4WithNextStepParams>;

impl<'a, E: Engine> ProverAssembly4WithNextStep<'a, E> {
    // this is a common function for standard and range plookup and basically computes s, witness and table polynomials
    fn make_plookup_variables(
        &self,
        witness_assignments: &[Polynomial<E::Fr, Values>],
        table_polynomials: &[&Box<dyn LookupTable<E::Fr>>],
        table_index_selector: &Polynomial<E::Fr, Values>,
        setup_polynomials: &[Polynomial<E::Fr, Values>],
        challenge: E::Fr,
        num_lookups: usize,
        worker: &Worker,
        is_range_lookup: bool,
    ) -> Result<[Polynomial<E::Fr, Values>; 3], SynthesisError> {
        // unpadded domain size
        let n = witness_assignments[0].as_ref().len();

        let s = {
            // construct s = (f,t) sorted by t
            // s = lookup_gates_len + lookup_table_len + padding_len
            // after sorting all padding will place up to top
            let mut total_row_size = num_lookups; // TODO:

            table_polynomials
                .iter()
                .for_each(|t| total_row_size += t.size());

            // aggregate lookup tables and gates together
            let mut s_vec: Vec<MultiSet<E::Fr>> = vec![MultiSet::new(); n - total_row_size];

            // sort([gates of table_1] + table_1) + sort([gates of table_2] + table_2) + .. sort([gates of table_n] + table_n)
            for lookup_table in table_polynomials.iter() {
                // sort each individual table and then append values into s_vec
                let mut s_intermediate = vec![];

                for ms in lookup_table.gates().iter() {
                    s_intermediate.push(ms.clone());
                }

                for (col1, col2, col3) in lookup_table.iter() {
                    s_intermediate.push(MultiSet::from_vec([
                        *col1,
                        *col2,
                        *col3,
                        lookup_table.lookup_table_type_as_fe(),
                    ]));
                }

                s_intermediate.sort();

                s_vec.extend_from_slice(&s_intermediate[..]);
            }

            let s_values: Vec<E::Fr> = s_vec
                .iter()
                .map(|m| m.scale_and_sum(challenge, is_range_lookup))
                .collect();

            let s = Polynomial::from_values_unpadded(s_values)?;

            s
        };

        let witness = {
            // f(x) = (a(x) + b(x)*challenge + c(x)*challenge^2 + index(x)*challenge^3) * q_lookup(x)
            let mut witness_assignments = witness_assignments[..3].iter().cloned();
            let mut witness_original = witness_assignments.next().unwrap();

            // range lookup use only single value so we do not need to linearise witness values
            if is_range_lookup {
                witness_original
            } else {
                let mut scalar = challenge.clone();
                for p in witness_assignments {
                    witness_original.add_assign_scaled(&worker, &p, &scalar);
                    scalar.mul_assign(&challenge);
                }

                witness_original.add_assign_scaled(&worker, &table_index_selector, &scalar);

                witness_original
            }
        };

        let table = {
            // t(x) = t_1(x) + t_2(x)*challenge + t_3(x)* challenge^2  + table_index*challenge^3
            assert_eq!(setup_polynomials.len(), 4);

            let mut lookup_table_polynomials = setup_polynomials.iter().cloned();

            let mut table_values = lookup_table_polynomials.next().unwrap();

            // range lookup use only single value so we do not need to linearise table values
            if is_range_lookup {
                table_values
            } else {
                let mut scalar = challenge.clone();
                for p in lookup_table_polynomials {
                    table_values.add_assign_scaled(&worker, &p, &scalar);
                    scalar.mul_assign(&challenge);
                }

                table_values
            }
        };

        Ok([s, witness, table])
    }

    fn compute_range_lookups<T: Transcript<E::Fr>, CP: CTPrecomputations<E::Fr>>(
        &self,
        transcript: &mut T,
        worker: &Worker,
        witness_assignments: &[Polynomial<E::Fr, Values>],
        setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
        crs_mon: &Crs<E, CrsForMonomialForm>,
        omegas_bitreversed: &CP,
        vanishing_polynomial: &Polynomial<E::Fr, Values>,
        plookup_challenge: E::Fr,
        beta: E::Fr,
        gamma: E::Fr,
    ) -> Result<LookupResult<E>, SynthesisError> {
        let n = self.n;

        let required_domain_size = n + 1;

        // we need `lookup_gate_selector`, `range_lookup_gate_selector` and `table_selector`  polynomials  for grand product computation
        let range_lookup_gate_selector_poly_index = setup.selector_polynomials.len() - 2;
        let range_lookup_gate_selector_poly =
            setup.selector_polynomials[range_lookup_gate_selector_poly_index].clone();
        let range_lookup_gate_selector = range_lookup_gate_selector_poly.clone().fft(worker);

        let table_selector_poly_index = setup.selector_polynomials.len() - 1;
        let table_selector_poly = setup.selector_polynomials[table_selector_poly_index].clone();
        let table_selector = table_selector_poly.clone().fft(worker);

        let mut unpadded_table_selector_evals = vec![];
        unpadded_table_selector_evals.extend_from_slice(&table_selector.as_ref()[..n]);
        let unpadded_table_selector =
            Polynomial::from_values_unpadded(unpadded_table_selector_evals)?;

        let mut range_lookup_tables = vec![];

        for lookup_table in self.lookup_tables.iter() {
            if lookup_table.lookup_type() == TableType::Range {
                range_lookup_tables.push(lookup_table);
            }
        }

        let range_lookup_table_values = setup.range_table_polynomials.clone();

        let mut range_lookup_table_values_in_monomial = vec![];

        for table_values in range_lookup_table_values.iter() {
            range_lookup_table_values_in_monomial
                .push(table_values.clone_padded_to_domain()?.ifft(&worker))
        }

        let mut beta_one = beta.clone();
        beta_one.add_assign(&E::Fr::one());

        let mut gamma_beta_one = beta_one.clone();
        gamma_beta_one.mul_assign(&gamma);

        let coset_factor = E::Fr::multiplicative_generator();

        let num_range_lookups = self.num_range_lookups;

        let [s_original, witness_original, table_original] = self.make_plookup_variables(
            &witness_assignments,
            &range_lookup_tables,
            &unpadded_table_selector,
            &range_lookup_table_values,
            plookup_challenge,
            num_range_lookups,
            worker,
            true,
        )?;

        // computation of grand product of range lookup

        //                       (\gamma + f(x)) * (\gamma + t(x))
        // Z(x*omega) = Z(x) * ----------------------------------------
        //                                (\gamma + s(x))

        let plookup_z = {
            let mut numerator_values = vec![E::Fr::one(); required_domain_size];
            let mut denominator_values = vec![E::Fr::one(); required_domain_size];

            let numerator_shifted = &mut numerator_values[1..];
            let denominator_shifted = &mut denominator_values[1..];

            worker.scope(required_domain_size, |scope, chunk| {
                for (((((denom, num), witness), lookup), table), s) in denominator_shifted
                    .as_mut()
                    .chunks_mut(chunk)
                    .zip(numerator_shifted.as_mut().chunks_mut(chunk))
                    .zip(witness_original.as_ref().chunks(chunk))
                    .zip(range_lookup_gate_selector.as_ref().chunks(chunk))
                    .zip(table_original.as_ref().chunks(chunk))
                    .zip(s_original.as_ref().chunks(chunk))
                {
                    scope.spawn(move |_| {
                        for (((((denom, num), witness), lookup), table), s) in denom
                            .iter_mut()
                            .zip(num.iter_mut())
                            .zip(witness.iter())
                            .zip(lookup.iter())
                            .zip(table.iter())
                            .zip(s.iter())
                        {
                            let mut numerator = witness.clone();
                            numerator.mul_assign(lookup);
                            numerator.add_assign(&gamma);
                            let mut tmp = table.clone();
                            tmp.add_assign(&gamma);
                            numerator.mul_assign(&tmp);

                            *num = numerator;

                            let mut denominator = s.clone();
                            denominator.add_assign(&gamma);

                            *denom = denominator;
                        }
                    });
                }
            });

            let numerator = Polynomial::from_values(numerator_values)?;
            let mut denominator = Polynomial::from_values(denominator_values)?;

            denominator.batch_inversion(&worker)?;
            denominator.mul_assign(&worker, &numerator);
            denominator = denominator.calculate_grand_product(&worker)?;

            let z = denominator.clone();

            let expected = gamma.pow([(n) as u64]);

            assert_eq!(z.as_ref()[0], E::Fr::one()); // z(X)*L_1(x) = 1
            assert_eq!(z.as_ref()[n], expected); // z(X*w)*L_{n-1}(x) = z(x)*L_n(x) = gamma^n

            z
        };

        let witness_in_monomial = witness_original.clone_padded_to_domain()?.ifft(&worker);
        let table_in_monomial = table_original.clone_padded_to_domain()?.ifft(&worker);
        let s_in_monomial = s_original.clone_padded_to_domain()?.ifft(&worker);
        let z_in_monomial = plookup_z.clone().ifft(&worker);
        let mut shifted_z_in_monomial = z_in_monomial.clone();
        shifted_z_in_monomial.distribute_powers(&worker, z_in_monomial.omega);

        // commit s poly
        let s_commitment = commit_using_monomials(&s_in_monomial.clone(), &crs_mon, &worker)?;
        commit_point_as_xy::<E, _>(transcript, &s_commitment);

        // commit grand product
        let z_commitment = commit_using_monomials(&z_in_monomial.clone(), &crs_mon, &worker)?;
        commit_point_as_xy::<E, _>(transcript, &z_commitment);

        let mut quotient_protos_bitreversed = vec![];
        for p in [
            witness_in_monomial.clone(),
            table_in_monomial.clone(),
            z_in_monomial.clone(),
            s_in_monomial.clone(),
            shifted_z_in_monomial,
        ]
        .iter()
        {
            let poly = p.clone();
            quotient_protos_bitreversed.push(poly.bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?);
        }

        let range_gate_selector_lde_4n_bitreversed = range_lookup_gate_selector_poly
            .bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?;
        // multiply witness and range selector
        quotient_protos_bitreversed[0].mul_assign(&worker, &range_gate_selector_lde_4n_bitreversed);

        // calculate plookup quotient polynomnial
        // lhs = Z(x)* (\gamma + f(x)) * (\gamma + t(x))
        // rhs = Z(x*omega) * (\gamma + s(x))
        // lhs - rhs = 0 mod Zh
        // t = (lhs - rhs)/Zh
        let quotient_bitreversed_lde = {
            let mut lhs = quotient_protos_bitreversed[0].clone();
            lhs.add_constant(&worker, &gamma);

            let mut tmp = quotient_protos_bitreversed[1].clone();
            tmp.add_constant(&worker, &gamma);
            lhs.mul_assign(&worker, &tmp);

            lhs.mul_assign(&worker, &quotient_protos_bitreversed[2]);

            let mut rhs = quotient_protos_bitreversed[3].clone();
            rhs.add_constant(&worker, &gamma);
            rhs.mul_assign(&worker, &quotient_protos_bitreversed[4]);

            let mut range_quotient_bitreversed = lhs.clone();
            range_quotient_bitreversed.sub_assign(&worker, &rhs);
            range_quotient_bitreversed.mul_assign(&worker, vanishing_polynomial);

            range_quotient_bitreversed
        };

        quotient_protos_bitreversed[0].bitreverse_enumeration(&worker);
        let witness_in_monomial_by_selector = quotient_protos_bitreversed[0]
            .clone()
            .icoset_fft_for_generator(&worker, &coset_factor);

        let result = LookupResult::<E> {
            challenge: plookup_challenge,
            quotient: quotient_bitreversed_lde,
            z_in_monomial: z_in_monomial,
            s_in_monomial: s_in_monomial,
            witness_in_monomial: witness_in_monomial_by_selector,
            table_values_in_monomial: table_in_monomial,
            tables_in_monomial: range_lookup_table_values_in_monomial,

            s_commitment: s_commitment,
            grand_product_commitment: z_commitment,
        };

        Ok(result)
    }

    fn compute_standard_lookups<T: Transcript<E::Fr>, CP: CTPrecomputations<E::Fr>>(
        &self,
        transcript: &mut T,
        worker: &Worker,
        witness_assignments: &[Polynomial<E::Fr, Values>],
        setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
        crs_mon: &Crs<E, CrsForMonomialForm>,
        omegas_bitreversed: &CP,
        vanishing_polynomial: &Polynomial<E::Fr, Values>,
        plookup_challenge: E::Fr,
        beta: E::Fr,
        gamma: E::Fr,
    ) -> Result<LookupResult<E>, SynthesisError> {
        let n = self.n;

        let required_domain_size = n + 1;

        // we need `lookup_gate_selector`, `range_lookup_gate_selector` and `table_selector`  polynomials  for grand product computation
        let lookup_gate_selector_poly_index = setup.selector_polynomials.len() - 3;
        let lookup_gate_selector_poly =
            setup.selector_polynomials[lookup_gate_selector_poly_index].clone();
        let lookup_gate_selector = lookup_gate_selector_poly.clone().fft(worker);

        let table_selector_poly_index = setup.selector_polynomials.len() - 1;
        let table_selector_poly = setup.selector_polynomials[table_selector_poly_index].clone();
        let table_selector = table_selector_poly.clone().fft(worker);

        let mut unpadded_table_selector_evals = vec![];
        unpadded_table_selector_evals.extend_from_slice(&table_selector.as_ref()[..n]);
        let unpadded_table_selector =
            Polynomial::from_values_unpadded(unpadded_table_selector_evals)?;

        let mut standard_lookup_tables = vec![];

        for lookup_table in self.lookup_tables.iter() {
            if lookup_table.lookup_type() != TableType::Range {
                standard_lookup_tables.push(lookup_table);
            }
        }

        let std_lookup_table_values = setup.lookup_table_polynomials.clone();

        let mut std_lookup_table_values_in_monomial = vec![];

        for table_values in std_lookup_table_values.iter() {
            std_lookup_table_values_in_monomial
                .push(table_values.clone_padded_to_domain()?.ifft(&worker))
        }

        let mut beta_one = beta.clone();
        beta_one.add_assign(&E::Fr::one());

        let mut gamma_beta_one = beta_one.clone();
        gamma_beta_one.mul_assign(&gamma);

        let coset_factor = E::Fr::multiplicative_generator();

        let num_standard_lookups = self.num_standard_lookups;

        let [s_original, witness_original, table_original] = self.make_plookup_variables(
            &witness_assignments,
            &standard_lookup_tables,
            &unpadded_table_selector,
            &std_lookup_table_values,
            plookup_challenge,
            num_standard_lookups,
            worker,
            false,
        )?;

        // since s_original has size n and n+1=required_domain_size we need to pad it to domain
        let s_in_monomial = s_original.clone_padded_to_domain()?.ifft(&worker);
        let mut shifted_s_in_monomial = s_in_monomial.clone();
        shifted_s_in_monomial.distribute_powers(&worker, s_in_monomial.omega);
        let shifted_s_original = shifted_s_in_monomial.clone().fft(&worker);

        // since table_original has size n and n+1=required_domain_size we need to pad it to domain
        let table_original_in_monomial = table_original.clone_padded_to_domain()?.ifft(&worker);
        let mut shifted_table_original_in_monomial = table_original_in_monomial.clone();
        shifted_table_original_in_monomial
            .distribute_powers(&worker, table_original_in_monomial.omega);
        let shifted_table_original = shifted_table_original_in_monomial.clone().fft(&worker);

        // computation of grand product of standard lookup

        //                          (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)
        // Z(x*omega) = Z(x)* -------------------------------------------------------------------------------------
        //                                  \gamma*(1 + \beta) + s(x) + \beta * s(x*omega)
        let plookup_z = {
            let mut numerator_values = vec![E::Fr::one(); required_domain_size];
            let mut denominator_values = vec![E::Fr::one(); required_domain_size];

            let numerator_shifted = &mut numerator_values[1..];
            let denominator_shifted = &mut denominator_values[1..];

            worker.scope(required_domain_size, |scope, chunk| {
                for (((((((denom, num), witness), lookup), shifted_table), table), shifted_s), s) in
                    denominator_shifted
                        .as_mut()
                        .chunks_mut(chunk)
                        .zip(numerator_shifted.as_mut().chunks_mut(chunk))
                        .zip(witness_original.as_ref().chunks(chunk))
                        .zip(lookup_gate_selector.as_ref().chunks(chunk))
                        .zip(shifted_table_original.as_ref().chunks(chunk))
                        .zip(table_original.as_ref().chunks(chunk))
                        .zip(shifted_s_original.as_ref().chunks(chunk))
                        .zip(s_original.as_ref().chunks(chunk))
                {
                    scope.spawn(move |_| {
                        for (
                            (
                                (((((denom, num), witness), lookup), shifted_table), table),
                                shifted_s,
                            ),
                            s,
                        ) in denom
                            .iter_mut()
                            .zip(num.iter_mut())
                            .zip(witness.iter())
                            .zip(lookup.iter())
                            .zip(shifted_table.iter())
                            .zip(table.iter())
                            .zip(shifted_s.iter())
                            .zip(s.iter())
                        {
                            let mut witness_part = witness.clone();
                            witness_part.mul_assign(lookup);
                            witness_part.add_assign(&gamma);

                            let mut table_part = shifted_table.clone();
                            table_part.mul_assign(&beta);
                            table_part.add_assign(&table);
                            table_part.add_assign(&gamma_beta_one);

                            let mut numerator = beta_one.clone();
                            numerator.mul_assign(&witness_part);
                            numerator.mul_assign(&table_part);

                            *num = numerator;

                            let mut denominator = shifted_s.clone();
                            denominator.mul_assign(&beta);
                            denominator.add_assign(&s);
                            denominator.add_assign(&gamma_beta_one);

                            *denom = denominator;
                        }
                    });
                }
            });

            let numerator = Polynomial::from_values(numerator_values)?;
            let mut denominator = Polynomial::from_values(denominator_values)?;

            denominator.batch_inversion(&worker)?;
            denominator.mul_assign(&worker, &numerator);
            denominator = denominator.calculate_grand_product(&worker)?;

            let z = denominator.clone();
            let expected = gamma_beta_one.pow([(n) as u64]);
            assert_eq!(z.as_ref()[0], E::Fr::one()); // z(X)*L_1(x) = 1
            assert_eq!(z.as_ref()[n], expected); // z(X*w)*L_{n-1}(x) = gamma*(beta+1)^n

            z
        };

        let z_in_monomial = plookup_z.ifft(&worker);

        // commit s poly
        let plookup_s_commitment =
            commit_using_monomials(&s_in_monomial.clone(), &crs_mon, &worker)?;
        commit_point_as_xy::<E, _>(transcript, &plookup_s_commitment);

        // commit grand product
        let plookup_z_commitment =
            commit_using_monomials(&z_in_monomial.clone(), &crs_mon, &worker)?;

        commit_point_as_xy::<E, _>(transcript, &plookup_z_commitment);

        let witness_in_monomial = witness_original.clone_padded_to_domain()?.ifft(&worker);
        let mut shifted_z_in_monomial = z_in_monomial.clone();
        shifted_z_in_monomial.distribute_powers(&worker, z_in_monomial.omega);

        let mut quotient_protos_bitreversed = vec![];
        for p in [
            witness_in_monomial.clone(),
            table_original_in_monomial.clone(),
            shifted_table_original_in_monomial,
            z_in_monomial.clone(),
            s_in_monomial.clone(),
            shifted_s_in_monomial,
            shifted_z_in_monomial,
        ]
        .iter()
        {
            let poly = p.clone();
            quotient_protos_bitreversed.push(poly.bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?);
        }

        let lookup_gate_selector_lde_4n_bitreversed = lookup_gate_selector_poly
            .bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?;

        quotient_protos_bitreversed[0]
            .mul_assign(&worker, &lookup_gate_selector_lde_4n_bitreversed);

        // calculate plookup quotient polynomnial
        // lhs = Z(x)* (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)
        // rhs = Z(x*omega) * (\gamma (1 + \beta) + s(x) + \beta * s(x*omega)
        // lhs - rhs = 0 mod Z_H
        // t = (lhs - rhs)/Z_H
        let lookup_std_quotient_lde_bitreversed = {
            let plookup_lhs_bitreversed = {
                let mut lhs = quotient_protos_bitreversed[0].clone();
                lhs.add_constant(&worker, &gamma);

                let mut tmp = quotient_protos_bitreversed[1].clone();
                tmp.add_assign_scaled(&worker, &quotient_protos_bitreversed[2], &beta);
                tmp.add_constant(&worker, &gamma_beta_one);

                lhs.mul_assign(&worker, &tmp);
                lhs.scale(&worker, beta_one);
                lhs.mul_assign(&worker, &quotient_protos_bitreversed[3]);

                lhs
            };

            let plookup_rhs_bitreversed = {
                let mut rhs = quotient_protos_bitreversed[4].clone();
                rhs.add_assign_scaled(&worker, &quotient_protos_bitreversed[5], &beta);
                rhs.add_constant(&worker, &gamma_beta_one);
                rhs.mul_assign(&worker, &quotient_protos_bitreversed[6]);

                rhs
            };

            let mut plookup_quotient_bitreversed = plookup_lhs_bitreversed.clone();
            plookup_quotient_bitreversed.sub_assign(&worker, &plookup_rhs_bitreversed);
            plookup_quotient_bitreversed.mul_assign(&worker, vanishing_polynomial);

            plookup_quotient_bitreversed
        };

        quotient_protos_bitreversed[0].bitreverse_enumeration(&worker);
        let witness_in_monomial_by_selector = quotient_protos_bitreversed[0]
            .clone()
            .icoset_fft_for_generator(&worker, &coset_factor);

        let result = LookupResult::<E> {
            challenge: plookup_challenge,
            quotient: lookup_std_quotient_lde_bitreversed,
            z_in_monomial: z_in_monomial,
            s_in_monomial: s_in_monomial,
            witness_in_monomial: witness_in_monomial_by_selector,
            table_values_in_monomial: table_original_in_monomial,
            tables_in_monomial: std_lookup_table_values_in_monomial,

            s_commitment: plookup_s_commitment,
            grand_product_commitment: plookup_z_commitment,
        };

        Ok(result)
    }

    fn compute_lookup<T: Transcript<E::Fr>, CP: CTPrecomputations<E::Fr>>(
        &self,
        transcript: &mut T,
        worker: &Worker,
        witness_assignments: &[Polynomial<E::Fr, Values>],
        setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
        crs_mon: &Crs<E, CrsForMonomialForm>,
        omegas_bitreversed: &CP,
        beta: E::Fr,
        gamma: E::Fr,
    ) -> Result<(Option<LookupResult<E>>, Option<LookupResult<E>>), SynthesisError> {
        assert!(self.is_table_initialized);

        let n = self.n;

        let required_domain_size = n + 1;

        let new_domain_size = required_domain_size * LDE_FACTOR;

        // vanishing of plookup is not consisting last element of domain so we need to cut it out
        // Z^{-1}(X) = (X - omega^(n)) / (X^(n+1) - 1)
        let vanishing_poly_for_lookup_quotient = calculate_inverse_vanishing_polynomial_in_a_coset::<
            E::Fr,
        >(
            &worker, new_domain_size, required_domain_size
        )?;
        let mut vanishing_poly_for_lookup_quotient_bitreversed =
            vanishing_poly_for_lookup_quotient.clone();
        vanishing_poly_for_lookup_quotient_bitreversed.bitreverse_enumeration(&worker);

        let mut std_lookup_found = false;
        let mut range_lookup_found = false;

        for lookup_table in self.lookup_tables.iter() {
            if lookup_table.lookup_type() == TableType::Range {
                range_lookup_found = true;
            } else {
                std_lookup_found = true;
            }
        }

        let mut std_result = None;
        let mut range_result = None;

        let plookup_challenge = transcript.get_challenge();

        if std_lookup_found {
            std_result = Some(self.compute_standard_lookups(
                transcript,
                worker,
                witness_assignments,
                setup,
                crs_mon,
                omegas_bitreversed,
                &vanishing_poly_for_lookup_quotient_bitreversed,
                plookup_challenge,
                beta,
                gamma,
            )?);
        }

        if range_lookup_found {
            range_result = Some(self.compute_range_lookups(
                transcript,
                worker,
                witness_assignments,
                setup,
                crs_mon,
                omegas_bitreversed,
                &vanishing_poly_for_lookup_quotient_bitreversed,
                plookup_challenge,
                beta,
                gamma,
            )?);
        }

        Ok((std_result, range_result))
    }

    pub fn prove<
        T: Transcript<E::Fr>,
        CP: CTPrecomputations<E::Fr>,
        CPI: CTPrecomputations<E::Fr>,
    >(
        &self,
        worker: &Worker,
        setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
        setup_precomputations: &SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>,
        crs_vals: &Crs<E, CrsForLagrangeForm>,
        crs_mon: &Crs<E, CrsForMonomialForm>,
        omegas_bitreversed: &CP,
        omegas_inv_bitreversed: &CPI,
    ) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
        use crate::pairing::CurveAffine;
        use std::sync::Arc;

        let mut transcript = T::new();

        assert!(self.is_finalized);

        let input_values = self.input_assingments.clone();

        for inp in input_values.iter() {
            transcript.commit_field_element(inp);
        }

        let n = self.n;
        let num_inputs = self.num_inputs;

        let required_domain_size = n + 1;
        assert!(required_domain_size.is_power_of_two());

        let full_assignments = self.get_witness_polynomials()?;

        let mut proof = Proof::<E, PlonkCsWidth4WithNextStepParams>::empty();
        let plookup_proof = &mut proof.plookup_proof;
        proof.n = n;
        proof.num_inputs = num_inputs;
        proof.input_values = input_values.clone();

        let coset_factor = E::Fr::multiplicative_generator();

        // let coset_factor = E::Fr::one();

        // Commit wire polynomials

        for wire_poly in full_assignments.iter() {
            let commitment = commit_using_raw_values(&wire_poly, &crs_vals, &worker)?;

            commit_point_as_xy::<E, _>(&mut transcript, &commitment);

            proof.wire_commitments.push(commitment);
        }

        // now transform assignments in the polynomials

        let mut assignment_polynomials = vec![];

        for p in full_assignments.clone().into_iter() {
            let p = Polynomial::from_values_unpadded(p)?;
            assignment_polynomials.push(p);
        }

        // make grand product polynomials

        // draw challenges for grand products

        let beta = transcript.get_challenge();
        let gamma = transcript.get_challenge();

        let mut grand_products_protos_with_gamma = assignment_polynomials.clone();

        // add gamma here to save computations later
        for p in grand_products_protos_with_gamma.iter_mut() {
            p.add_constant(&worker, &gamma);
        }

        let domain = Domain::new_for_size(required_domain_size as u64)?;

        let mut domain_elements =
            materialize_domain_elements_with_natural_enumeration(&domain, &worker);

        domain_elements
            .pop()
            .expect("must pop last element for omega^i");

        let mut domain_elements_poly_by_beta =
            Polynomial::from_values_unpadded(domain_elements.clone())?;
        domain_elements_poly_by_beta.scale(&worker, beta);

        let non_residues = make_non_residues::<E::Fr>(
            <PlonkCsWidth4WithNextStepParams as PlonkConstraintSystemParams<E>>::STATE_WIDTH - 1,
            &domain,
        );

        // we take A, B, C, ... values and form (A + beta * X * non_residue + gamma), etc and calculate their grand product

        let mut z_num = {
            let mut grand_products_proto_it = grand_products_protos_with_gamma.iter().cloned();

            let mut z_1 = grand_products_proto_it.next().unwrap();
            z_1.add_assign(&worker, &domain_elements_poly_by_beta);

            for (mut p, non_res) in grand_products_proto_it.zip(non_residues.iter()) {
                p.add_assign_scaled(&worker, &domain_elements_poly_by_beta, non_res);
                z_1.mul_assign(&worker, &p);
            }

            z_1
        };

        // we take A, B, C, ... values and form (A + beta * perm_a + gamma), etc and calculate their grand product

        let z_den = {
            assert_eq!(
                setup_precomputations
                    .permutation_polynomials_values_of_size_n_minus_one
                    .len(),
                grand_products_protos_with_gamma.len()
            );
            let mut grand_products_proto_it = grand_products_protos_with_gamma.into_iter();
            let mut permutation_polys_it = setup_precomputations
                .permutation_polynomials_values_of_size_n_minus_one
                .iter();

            let mut z_2 = grand_products_proto_it.next().unwrap();
            z_2.add_assign_scaled(&worker, &permutation_polys_it.next().unwrap(), &beta);

            for (mut p, perm) in grand_products_proto_it.zip(permutation_polys_it) {
                // permutation polynomials
                p.add_assign_scaled(&worker, &perm, &beta);
                z_2.mul_assign(&worker, &p);
            }

            z_2.batch_inversion(&worker)?;

            z_2
        };

        z_num.mul_assign(&worker, &z_den);
        drop(z_den);

        let z = z_num.calculate_shifted_grand_product(&worker)?;

        assert!(z.size().is_power_of_two());

        assert!(z.as_ref()[0] == E::Fr::one());
        // println!("Z last = {}", z.as_ref().last().unwrap());
        // assert!(z.as_ref().last().expect("must exist") == &E::Fr::one());

        let z_commitment = commit_using_values(&z, &crs_vals, &worker)?;
        proof.grand_product_commitment = z_commitment;

        commit_point_as_xy::<E, _>(&mut transcript, &proof.grand_product_commitment);

        // interpolate on the main domain
        let z_in_monomial_form =
            z.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // those are z(x*Omega) formally
        let mut z_shifted_in_monomial_form = z_in_monomial_form.clone();
        z_shifted_in_monomial_form.distribute_powers(&worker, z_in_monomial_form.omega);

        // now we have to LDE everything and compute quotient polynomial
        // also to save on openings that we will have to do from the monomial form anyway

        let mut witness_polys_in_monomial_form = vec![];

        let mut witness_ldes_on_coset = vec![];
        let mut witness_next_ldes_on_coset = vec![];

        for (idx, w) in assignment_polynomials.clone().into_iter().enumerate() {
            let monomial = w.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                &worker,
                omegas_inv_bitreversed,
                &E::Fr::one(),
            )?;
            witness_polys_in_monomial_form.push(monomial.clone());

            // this is D polynomial and we need to make next
            if idx
                == <PlonkCsWidth4WithNextStepParams as PlonkConstraintSystemParams<E>>::STATE_WIDTH
                    - 1
            {
                let mut d_next = monomial.clone();
                d_next.distribute_powers(&worker, d_next.omega);

                let lde = d_next.bitreversed_lde_using_bitreversed_ntt(
                    &worker,
                    LDE_FACTOR,
                    omegas_bitreversed,
                    &coset_factor,
                )?;

                witness_next_ldes_on_coset.push(lde);
            }

            let lde = monomial.bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?;
            witness_ldes_on_coset.push(lde);
        }

        // PLOOKUP
        let mut std_lookup_result = None;
        let mut range_lookup_result = None;

        if self.is_table_initialized {
            let (std_result, range_result) = self.compute_lookup(
                &mut transcript,
                worker,
                &assignment_polynomials,
                setup,
                crs_mon,
                omegas_bitreversed,
                beta,
                gamma,
            )?;

            std_lookup_result = std_result;
            range_lookup_result = range_result;
        }

        let alpha = transcript.get_challenge();

        // calculate first part of the quotient polynomial - the gate itself
        // A + B + C + D + AB + CONST + D_NEXT == 0 everywhere but on the last point of the domain

        // after introducing new lookup selector, constant selector is shifted one step to the left
        let selector_q_const_index = setup.selector_polynomials.len() - 4;

        let mut quotient_linearization_challenge = E::Fr::one();

        let (mut t_1, mut tmp) = {
            // Include the public inputs
            let mut inputs_poly = Polynomial::<E::Fr, Values>::new_for_size(required_domain_size)?;
            for (idx, &input) in input_values.iter().enumerate() {
                inputs_poly.as_mut()[idx] = input;
            }
            // go into monomial form

            let mut inputs_poly = inputs_poly.ifft_using_bitreversed_ntt(
                &worker,
                omegas_inv_bitreversed,
                &E::Fr::one(),
            )?;

            // add constants selectors vector
            inputs_poly.add_assign(&worker, &setup.selector_polynomials[selector_q_const_index]);

            // LDE
            let mut t_1 = inputs_poly.bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?;

            // Q_A * A
            let mut tmp = setup_precomputations
                .selector_polynomials_on_coset_of_size_4n_bitreversed[0]
                .clone();
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            t_1.add_assign(&worker, &tmp);

            // Q_B * B
            tmp.reuse_allocation(
                &setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[1],
            );
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            // Q_C * C
            tmp.reuse_allocation(
                &setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[2],
            );
            tmp.mul_assign(&worker, &witness_ldes_on_coset[2]);
            t_1.add_assign(&worker, &tmp);

            // Q_D * D
            tmp.reuse_allocation(
                &setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[3],
            );
            tmp.mul_assign(&worker, &witness_ldes_on_coset[3]);
            t_1.add_assign(&worker, &tmp);

            // Q_M * A * B
            tmp.reuse_allocation(
                &setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[4],
            );
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            tmp.reuse_allocation(
                &setup_precomputations
                    .next_step_selector_polynomials_on_coset_of_size_4n_bitreversed[0],
            );
            tmp.mul_assign(&worker, &witness_next_ldes_on_coset[0]);
            t_1.add_assign(&worker, &tmp);

            (t_1, tmp)
        };

        // drop(witness_ldes_on_coset);
        drop(witness_next_ldes_on_coset);

        // now compute the permutation argument

        let z_coset_lde_bitreversed = z_in_monomial_form
            .clone()
            .bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?;

        assert!(z_coset_lde_bitreversed.size() == required_domain_size * LDE_FACTOR);

        let z_shifted_coset_lde_bitreversed = z_shifted_in_monomial_form
            .bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?;

        assert!(z_shifted_coset_lde_bitreversed.size() == required_domain_size * LDE_FACTOR);

        // For both Z_1 and Z_2 we first check for grand products
        // z*(X)(A + beta*X + gamma)(B + beta*k_1*X + gamma)(C + beta*K_2*X + gamma) -
        // - (A + beta*perm_a(X) + gamma)(B + beta*perm_b(X) + gamma)(C + beta*perm_c(X) + gamma)*Z(X*Omega)== 0

        // we use evaluations of the polynomial X and K_i * X on a large domain's coset

        quotient_linearization_challenge.mul_assign(&alpha);

        {
            let mut contrib_z = z_coset_lde_bitreversed.clone();

            // A + beta*X + gamma

            tmp.reuse_allocation(&witness_ldes_on_coset[0]);
            tmp.add_constant(&worker, &gamma);
            tmp.add_assign_scaled(
                &worker,
                &setup_precomputations.x_on_coset_of_size_4n_bitreversed,
                &beta,
            );
            contrib_z.mul_assign(&worker, &tmp);

            assert_eq!(non_residues.len() + 1, witness_ldes_on_coset.len());

            for (w, non_res) in witness_ldes_on_coset[1..].iter().zip(non_residues.iter()) {
                let mut factor = beta;
                factor.mul_assign(&non_res);

                tmp.reuse_allocation(&w);
                tmp.add_constant(&worker, &gamma);
                tmp.add_assign_scaled(
                    &worker,
                    &setup_precomputations.x_on_coset_of_size_4n_bitreversed,
                    &factor,
                );
                contrib_z.mul_assign(&worker, &tmp);
            }

            t_1.add_assign_scaled(&worker, &contrib_z, &quotient_linearization_challenge);

            drop(contrib_z);

            let mut contrib_z = z_shifted_coset_lde_bitreversed;

            // A + beta*perm_a + gamma

            assert_eq!(
                setup_precomputations
                    .permutation_polynomials_on_coset_of_size_4n_bitreversed
                    .len(),
                witness_ldes_on_coset.len()
            );

            for (w, perm) in witness_ldes_on_coset.iter().zip(
                setup_precomputations
                    .permutation_polynomials_on_coset_of_size_4n_bitreversed
                    .iter(),
            ) {
                tmp.reuse_allocation(&w);
                tmp.add_constant(&worker, &gamma);
                tmp.add_assign_scaled(&worker, &perm, &beta);
                contrib_z.mul_assign(&worker, &tmp);
            }

            t_1.sub_assign_scaled(&worker, &contrib_z, &quotient_linearization_challenge);

            drop(contrib_z);
        }

        quotient_linearization_challenge.mul_assign(&alpha);

        // z(omega^0) - 1 == 0

        let l_0 =
            calculate_lagrange_poly::<E::Fr>(&worker, required_domain_size.next_power_of_two(), 0)?;

        {
            let mut z_minus_one_by_l_0 = z_coset_lde_bitreversed;
            z_minus_one_by_l_0.sub_constant(&worker, &E::Fr::one());

            let l_coset_lde_bitreversed = l_0.bitreversed_lde_using_bitreversed_ntt(
                &worker,
                LDE_FACTOR,
                omegas_bitreversed,
                &coset_factor,
            )?;

            z_minus_one_by_l_0.mul_assign(&worker, &l_coset_lde_bitreversed);

            t_1.add_assign_scaled(
                &worker,
                &z_minus_one_by_l_0,
                &quotient_linearization_challenge,
            );

            drop(z_minus_one_by_l_0);
        }

        drop(tmp);

        t_1.mul_assign(
            &worker,
            &setup_precomputations.inverse_divisor_on_coset_of_size_4n_bitreversed,
        );

        if std_lookup_result.is_some() {
            // std range quotient
            quotient_linearization_challenge.mul_assign(&alpha);
            let mut lookup_std_quotient_lde_bitreversed =
                std_lookup_result.clone().unwrap().quotient.clone();
            lookup_std_quotient_lde_bitreversed.scale(&worker, quotient_linearization_challenge);
            t_1.add_assign(&worker, &lookup_std_quotient_lde_bitreversed);
        }

        if range_lookup_result.is_some() {
            // lookup range quotient
            quotient_linearization_challenge.mul_assign(&alpha);
            let mut lookup_range_quotient_lde_bitreversed =
                range_lookup_result.clone().unwrap().quotient.clone();
            lookup_range_quotient_lde_bitreversed.scale(&worker, quotient_linearization_challenge);
            t_1.add_assign(&worker, &lookup_range_quotient_lde_bitreversed);
        }

        t_1.bitreverse_enumeration(&worker);

        let t_poly_in_monomial_form =
            t_1.icoset_fft_for_generator(&worker, &E::Fr::multiplicative_generator());

        let mut t_poly_parts =
            t_poly_in_monomial_form.break_into_multiples(required_domain_size)?;

        for t_part in t_poly_parts.iter() {
            let t_part_commitment = commit_using_monomials(&t_part, &crs_mon, &worker)?;

            commit_point_as_xy::<E, _>(&mut transcript, &t_part_commitment);

            proof.quotient_poly_commitments.push(t_part_commitment);
        }

        let z = transcript.get_challenge();
        let mut z_by_omega = z;
        z_by_omega.mul_assign(&domain.generator);

        // draw random point

        for (idx, p) in witness_polys_in_monomial_form.iter().enumerate() {
            let value_at_z = p.evaluate_at(&worker, z);
            proof.wire_values_at_z.push(value_at_z);
            if idx == 3 {
                let value_at_z_omega = p.evaluate_at(&worker, z_by_omega);
                proof.wire_values_at_z_omega.push(value_at_z_omega);
            }
        }

        for p in setup.permutation_polynomials[..(setup.permutation_polynomials.len() - 1)].iter() {
            let value_at_z = p.evaluate_at(&worker, z);
            proof.permutation_polynomials_at_z.push(value_at_z);
        }

        let z_at_z_omega = z_in_monomial_form.evaluate_at(&worker, z_by_omega);
        proof.grand_product_at_z_omega = z_at_z_omega;

        let t_at_z = {
            let mut result = E::Fr::zero();
            let mut current = E::Fr::one();
            let z_in_domain_size = z.pow(&[required_domain_size as u64]);
            for p in t_poly_parts.iter() {
                let mut subvalue_at_z = p.evaluate_at(&worker, z);
                subvalue_at_z.mul_assign(&current);
                result.add_assign(&subvalue_at_z);
                current.mul_assign(&z_in_domain_size);
            }

            result
        };

        // evaluations of plookup
        {
            let table_selector_poly_index = setup.selector_polynomials.len() - 1;

            if std_lookup_result.is_some() {
                let lookup_result = std_lookup_result.clone().unwrap();

                let lookup_gate_selector_poly_index = setup.selector_polynomials.len() - 3;

                plookup_proof.std_s_commitment = lookup_result.s_commitment.clone();
                plookup_proof.std_grand_product_commitment =
                    lookup_result.grand_product_commitment.clone();

                // Z(x*w) * (\gamma + s(x) + \beta*s(x*w)) - Z(x) *(\gamma + f(x)) * (\gamma + t(x) + \beta*t(x*w))
                plookup_proof.std_grand_product_at_z_omega =
                    lookup_result.z_in_monomial.evaluate_at(&worker, z_by_omega);
                plookup_proof.std_s_at_z = lookup_result.s_in_monomial.evaluate_at(&worker, z);
                plookup_proof.std_shifted_s_at_z =
                    lookup_result.s_in_monomial.evaluate_at(&worker, z_by_omega);

                plookup_proof.std_grand_product_at_z =
                    lookup_result.z_in_monomial.evaluate_at(&worker, z);
                plookup_proof.std_lookup_table_id_selector_at_z =
                    setup.selector_polynomials[table_selector_poly_index].evaluate_at(&worker, z);
                plookup_proof.std_lookup_selector_at_z = setup.selector_polynomials
                    [lookup_gate_selector_poly_index]
                    .evaluate_at(&worker, z);

                for (i, table_poly) in lookup_result.tables_in_monomial.iter().enumerate() {
                    plookup_proof.std_table_columns_at_z[i] = table_poly.evaluate_at(&worker, z);
                    plookup_proof.std_shifted_table_columns_at_z[i] =
                        table_poly.evaluate_at(&worker, z_by_omega);
                }
            }

            if range_lookup_result.is_some() {
                let lookup_result = range_lookup_result.clone().unwrap();

                let range_lookup_gate_selector_poly_index = setup.selector_polynomials.len() - 2;

                plookup_proof.range_s_commitment = lookup_result.s_commitment.clone();
                plookup_proof.range_grand_product_commitment =
                    lookup_result.grand_product_commitment.clone();

                // Z(x*w) * (\gamma + s(x)) - Z(x) *(\gamma + f(x)) * (\gamma + t(x))
                plookup_proof.range_grand_product_at_z_omega =
                    lookup_result.z_in_monomial.evaluate_at(&worker, z_by_omega);
                plookup_proof.range_s_at_z = lookup_result.s_in_monomial.evaluate_at(&worker, z);

                plookup_proof.range_grand_product_at_z =
                    lookup_result.z_in_monomial.evaluate_at(&worker, z);
                plookup_proof.range_lookup_table_id_selector_at_z =
                    setup.selector_polynomials[table_selector_poly_index].evaluate_at(&worker, z);
                plookup_proof.range_lookup_selector_at_z = setup.selector_polynomials
                    [range_lookup_gate_selector_poly_index]
                    .evaluate_at(&worker, z);

                for (i, table_poly) in lookup_result.tables_in_monomial.iter().enumerate() {
                    plookup_proof.range_table_columns_at_z[i] = table_poly.evaluate_at(&worker, z);
                }
            }
        }

        proof.quotient_polynomial_at_z = t_at_z;

        // append evaluations into transcript

        for el in proof.wire_values_at_z.iter() {
            transcript.commit_field_element(el);
        }

        for el in proof.wire_values_at_z_omega.iter() {
            transcript.commit_field_element(el);
        }

        for el in proof.permutation_polynomials_at_z.iter() {
            transcript.commit_field_element(el);
        }

        // append plookup evaluations into transcript
        {
            if std_lookup_result.is_some() {
                transcript.commit_field_element(&plookup_proof.std_lookup_selector_at_z);
                transcript.commit_field_element(&plookup_proof.std_lookup_table_id_selector_at_z);
                transcript.commit_field_element(&plookup_proof.std_grand_product_at_z);
                transcript.commit_field_element(&plookup_proof.std_grand_product_at_z_omega);
                transcript.commit_field_element(&plookup_proof.std_s_at_z);
                transcript.commit_field_element(&plookup_proof.std_shifted_s_at_z);

                for el in plookup_proof.std_table_columns_at_z.iter() {
                    transcript.commit_field_element(el);
                }

                for el in plookup_proof.std_shifted_table_columns_at_z.iter() {
                    transcript.commit_field_element(el);
                }
            }

            if range_lookup_result.is_some() {
                transcript.commit_field_element(&plookup_proof.range_lookup_selector_at_z);
                transcript.commit_field_element(&plookup_proof.range_lookup_table_id_selector_at_z);
                transcript.commit_field_element(&plookup_proof.range_grand_product_at_z);
                transcript.commit_field_element(&plookup_proof.range_grand_product_at_z_omega);
                transcript.commit_field_element(&plookup_proof.range_s_at_z);

                for el in plookup_proof.range_table_columns_at_z.iter() {
                    transcript.commit_field_element(el);
                }
            }
        }

        transcript.commit_field_element(&proof.quotient_polynomial_at_z);

        // now compute linearization_polynomial in a monomial form

        let mut quotient_linearization_challenge = E::Fr::one();

        let r = {
            // Q_const
            let mut r = setup.selector_polynomials[selector_q_const_index].clone();

            // Q_A * A(z)
            r.add_assign_scaled(
                &worker,
                &setup.selector_polynomials[0],
                &proof.wire_values_at_z[0],
            );

            // Q_B * B(z)
            r.add_assign_scaled(
                &worker,
                &setup.selector_polynomials[1],
                &proof.wire_values_at_z[1],
            );

            // Q_C * C(z)
            r.add_assign_scaled(
                &worker,
                &setup.selector_polynomials[2],
                &proof.wire_values_at_z[2],
            );

            // Q_D * D(z)
            r.add_assign_scaled(
                &worker,
                &setup.selector_polynomials[3],
                &proof.wire_values_at_z[3],
            );

            // Q_M * A(z) * B(z)
            let mut scaling_factor = proof.wire_values_at_z[0];
            scaling_factor.mul_assign(&proof.wire_values_at_z[1]);
            r.add_assign_scaled(&worker, &setup.selector_polynomials[4], &scaling_factor);

            // Q_D_Next * D(z*omega)

            r.add_assign_scaled(
                &worker,
                &setup.next_step_selector_polynomials[0],
                &proof.wire_values_at_z_omega[0],
            );

            quotient_linearization_challenge.mul_assign(&alpha);

            // + (a(z) + beta*z + gamma)*()*()*()*Z(x)

            let mut factor = quotient_linearization_challenge;
            for (wire_at_z, non_residue) in proof
                .wire_values_at_z
                .iter()
                .zip(Some(E::Fr::one()).iter().chain(&non_residues))
            {
                let mut t = z;
                t.mul_assign(&non_residue);
                t.mul_assign(&beta);
                t.add_assign(&wire_at_z);
                t.add_assign(&gamma);

                factor.mul_assign(&t);
            }

            r.add_assign_scaled(&worker, &z_in_monomial_form, &factor);

            // - (a(z) + beta*perm_a + gamma)*()*()*z(z*omega) * beta * perm_d(X)

            let mut factor = quotient_linearization_challenge;
            factor.mul_assign(&beta);
            factor.mul_assign(&z_at_z_omega);

            for (wire_at_z, perm_at_z) in proof
                .wire_values_at_z
                .iter()
                .zip(proof.permutation_polynomials_at_z.iter())
            {
                let mut t = *perm_at_z;
                t.mul_assign(&beta);
                t.add_assign(&wire_at_z);
                t.add_assign(&gamma);

                factor.mul_assign(&t);
            }

            r.sub_assign_scaled(
                &worker,
                &setup
                    .permutation_polynomials
                    .last()
                    .expect("last permutation poly"),
                &factor,
            );

            // + L_0(z) * Z(x)

            quotient_linearization_challenge.mul_assign(&alpha);

            let mut factor = evaluate_l0_at_point(required_domain_size as u64, z)?;
            factor.mul_assign(&quotient_linearization_challenge);

            r.add_assign_scaled(&worker, &z_in_monomial_form, &factor);

            r
        };

        // commit the linearization polynomial

        let r_at_z = r.evaluate_at(&worker, z);
        proof.linearization_polynomial_at_z = r_at_z;

        transcript.commit_field_element(&proof.linearization_polynomial_at_z);

        // sanity check - verification
        {
            let lhs = t_at_z;

            let mut quotient_linearization_challenge = E::Fr::one();

            let mut rhs = r_at_z;

            // add public inputs
            {
                for (idx, input) in input_values.iter().enumerate() {
                    let mut tmp = evaluate_lagrange_poly_at_point(idx, &domain, z)?;
                    tmp.mul_assign(&input);

                    rhs.add_assign(&tmp);
                }
            }

            quotient_linearization_challenge.mul_assign(&alpha);

            // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

            let mut z_part = z_at_z_omega;

            assert_eq!(
                proof.permutation_polynomials_at_z.len() + 1,
                proof.wire_values_at_z.len()
            );

            for (w, p) in proof
                .wire_values_at_z
                .iter()
                .zip(proof.permutation_polynomials_at_z.iter())
            {
                let mut tmp = *p;
                tmp.mul_assign(&beta);
                tmp.add_assign(&gamma);
                tmp.add_assign(&w);

                z_part.mul_assign(&tmp);
            }

            // last poly value and gamma
            let mut tmp = gamma;
            tmp.add_assign(&proof.wire_values_at_z.iter().rev().next().unwrap());

            z_part.mul_assign(&tmp);
            z_part.mul_assign(&quotient_linearization_challenge);

            rhs.sub_assign(&z_part);

            quotient_linearization_challenge.mul_assign(&alpha);

            // - L_0(z) * \alpha^2

            let mut l_0_at_z = evaluate_l0_at_point(required_domain_size as u64, z)?;
            l_0_at_z.mul_assign(&quotient_linearization_challenge);

            rhs.sub_assign(&l_0_at_z);

            let vanishing_at_z = evaluate_vanishing_for_size(&z, required_domain_size as u64)
                .inverse()
                .unwrap();
            rhs.mul_assign(&vanishing_at_z);

            // plookup checks
            let vanishing_for_lookup_at_z =
                evaluate_inverse_vanishing_poly_with_last_point_cut(required_domain_size, z);

            let mut beta_one = beta.clone();
            beta_one.add_assign(&E::Fr::one());

            let mut gamma_beta_one = beta_one.clone();
            gamma_beta_one.mul_assign(&gamma);

            // std lookup checks
            if std_lookup_result.is_some() {
                let lookup_result = std_lookup_result.clone().unwrap();

                let plookup_challenge = lookup_result.challenge.clone();

                // f(z) = (a(z) + b(z)*challenge + c(z)*challenge^2 + table_id(z)*challenge^3)*q_lookup(z)
                let mut witness_part = E::Fr::zero();
                let mut scalar = E::Fr::one();
                let wire_values_at_z = &proof.wire_values_at_z[0..3];
                for p in wire_values_at_z.iter() {
                    let mut tmp = p.clone();
                    tmp.mul_assign(&scalar);
                    witness_part.add_assign(&tmp);
                    scalar.mul_assign(&plookup_challenge);
                }

                let mut table_id_by_challenge =
                    plookup_proof.std_lookup_table_id_selector_at_z.clone(); // TODO use single table id
                table_id_by_challenge.mul_assign(&scalar);
                witness_part.add_assign(&table_id_by_challenge);
                witness_part.mul_assign(&plookup_proof.std_lookup_selector_at_z);

                let expected_witness = lookup_result.witness_in_monomial.evaluate_at(&worker, z);
                assert_eq!(witness_part, expected_witness);
                witness_part.add_assign(&gamma);

                // t(z*w) = (t1(z*w) + t2(z*w)*challenge + t3(z*w)*challenge^2 + table_id(z*w)*challenge^3)
                let mut table_part = E::Fr::zero();

                let mut scalar = E::Fr::one();
                for p in plookup_proof.std_shifted_table_columns_at_z.iter() {
                    let mut tmp = p.clone();
                    tmp.mul_assign(&scalar);
                    table_part.add_assign(&tmp);
                    scalar.mul_assign(&plookup_challenge);
                }
                let expected_shifted_table = lookup_result
                    .table_values_in_monomial
                    .evaluate_at(&worker, z_by_omega);
                assert_eq!(table_part, expected_shifted_table);
                table_part.mul_assign(&beta);

                let mut tmp_table_part = E::Fr::zero();
                let mut scalar = E::Fr::one();
                for p in plookup_proof.std_table_columns_at_z.iter() {
                    let mut tmp = p.clone();
                    tmp.mul_assign(&scalar);
                    tmp_table_part.add_assign(&tmp);
                    scalar.mul_assign(&plookup_challenge);
                }
                let expected_table = lookup_result
                    .table_values_in_monomial
                    .evaluate_at(&worker, z);
                assert_eq!(tmp_table_part, expected_table);

                table_part.add_assign(&tmp_table_part);
                table_part.add_assign(&gamma_beta_one);

                // Z(z)*(1+\beta)*(\gamma + f(z)) * (\gama(\beta + 1) + t(z) + t(z*w))
                let mut lookup_lhs = plookup_proof.std_grand_product_at_z.clone();
                lookup_lhs.mul_assign(&witness_part);
                lookup_lhs.mul_assign(&table_part);
                lookup_lhs.mul_assign(&beta_one);

                // - Z(z*w)*(\gamma(\beta+1) + t(z) + t(z*w))
                let mut s_part = plookup_proof.std_shifted_s_at_z.clone();
                s_part.mul_assign(&beta);
                s_part.add_assign(&plookup_proof.std_s_at_z);
                s_part.add_assign(&gamma_beta_one);

                let mut lookup_rhs = plookup_proof.std_grand_product_at_z_omega.clone();
                lookup_rhs.mul_assign(&s_part);

                lookup_lhs.sub_assign(&lookup_rhs);

                lookup_lhs.mul_assign(&vanishing_for_lookup_at_z);

                quotient_linearization_challenge.mul_assign(&alpha);
                lookup_lhs.mul_assign(&quotient_linearization_challenge);

                rhs.add_assign(&lookup_lhs);
            };

            // range lookup checks

            if range_lookup_result.is_some() {
                let lookup_result = range_lookup_result.unwrap();

                let plookup_challenge = lookup_result.challenge.clone();
                // f(z) = (a(z) + b(z)*challenge + c(z)*challenge^2 + table_id(z)*challenge^3)*q_lookup(z)
                let mut witness_part = E::Fr::zero();
                let mut scalar = E::Fr::one();
                let wire_values_at_z = &proof.wire_values_at_z[0..1];
                for p in wire_values_at_z.iter() {
                    let mut tmp = p.clone();
                    tmp.mul_assign(&scalar);
                    witness_part.add_assign(&tmp);
                    scalar.mul_assign(&plookup_challenge);
                }

                let mut table_id_by_challenge =
                    plookup_proof.range_lookup_table_id_selector_at_z.clone();
                table_id_by_challenge.mul_assign(&scalar);
                witness_part.mul_assign(&plookup_proof.range_lookup_selector_at_z);

                let expected_witness = lookup_result.witness_in_monomial.evaluate_at(&worker, z);
                assert_eq!(witness_part, expected_witness);

                witness_part.add_assign(&gamma);

                // t(z) = (t1(z) + t2(z)*challenge + t3(z)*challenge^2 + table_id(z)*challenge^3)
                // t2(z)m t3(z) are zero
                assert_eq!(plookup_proof.range_table_columns_at_z[1], E::Fr::zero());
                assert_eq!(plookup_proof.range_table_columns_at_z[2], E::Fr::zero());
                let mut table_part = E::Fr::zero();
                let mut scalar = E::Fr::one();
                for p in plookup_proof.range_table_columns_at_z[..1].iter() {
                    let mut tmp = p.clone();
                    tmp.mul_assign(&scalar);
                    table_part.add_assign(&tmp);
                    scalar.mul_assign(&plookup_challenge);
                }

                let expected_table = lookup_result
                    .table_values_in_monomial
                    .evaluate_at(&worker, z);
                assert_eq!(table_part, expected_table);
                table_part.add_assign(&gamma);

                let mut lookup_rhs = plookup_proof.range_grand_product_at_z.clone();
                lookup_rhs.mul_assign(&witness_part);
                lookup_rhs.mul_assign(&table_part);

                let mut tmp = plookup_proof.range_s_at_z.clone();
                tmp.add_assign(&gamma);
                tmp.mul_assign(&plookup_proof.range_grand_product_at_z_omega);
                lookup_rhs.sub_assign(&tmp);

                lookup_rhs.mul_assign(&vanishing_for_lookup_at_z);

                quotient_linearization_challenge.mul_assign(&alpha);
                lookup_rhs.mul_assign(&quotient_linearization_challenge);
                rhs.add_assign(&lookup_rhs);
            }

            if lhs != rhs {
                println!("sanity check failed");
                return Err(SynthesisError::Unsatisfiable);
            }
        }

        // get multiopening challenge

        let v = transcript.get_challenge();

        // open at z:
        // t_i(x) * z^{domain_size*i}
        // r(x)
        // witnesses
        // permutations except of the last one

        // open at z*omega:
        // z(x)
        // next step witnesses (if any)

        let mut multiopening_challenge = E::Fr::one();

        let mut poly_to_divide_at_z = t_poly_parts.drain(0..1).collect::<Vec<_>>().pop().unwrap();
        let z_in_domain_size = z.pow(&[required_domain_size as u64]);
        let mut power_of_z = z_in_domain_size;
        for t_part in t_poly_parts.into_iter() {
            poly_to_divide_at_z.add_assign_scaled(&worker, &t_part, &power_of_z);
            power_of_z.mul_assign(&z_in_domain_size);
        }

        // open quotient poly by using parts
        // (for debugging)
        // t1(x) + t2(x) + t3(x) t4(x) - z
        // ---------------------------
        //          x-z
        //
        // 1. sum parts in monomial
        // 2. sub z (does not necessary)
        // 3. quotient by dividing at z
        // 4. commit quotient (this is proof)
        // 5. store in proof

        let t_sum = poly_to_divide_at_z.clone();

        let t_quotient = Polynomial::from_coeffs(divide_single::<E>(t_sum.as_ref(), z))?;
        plookup_proof.t_opening_proof = commit_using_monomials(&t_quotient, &crs_mon, &worker)?;

        // linearization polynomial
        multiopening_challenge.mul_assign(&v);
        poly_to_divide_at_z.add_assign_scaled(&worker, &r, &multiopening_challenge);

        debug_assert_eq!(multiopening_challenge, v.pow(&[1 as u64]));

        // all witness polys
        for w in witness_polys_in_monomial_form.iter() {
            multiopening_challenge.mul_assign(&v);
            poly_to_divide_at_z.add_assign_scaled(&worker, &w, &multiopening_challenge);
        }

        debug_assert_eq!(multiopening_challenge, v.pow(&[(1 + 4) as u64]));

        // all except of the last permutation polys
        for p in setup.permutation_polynomials[..(setup.permutation_polynomials.len() - 1)].iter() {
            multiopening_challenge.mul_assign(&v);
            poly_to_divide_at_z.add_assign_scaled(&worker, &p, &multiopening_challenge);
        }

        debug_assert_eq!(multiopening_challenge, v.pow(&[(1 + 4 + 3) as u64]));

        {
            // open lookup grand product at z for debugging
            let quotient_of_lookup_z = Polynomial::from_coeffs(divide_single::<E>(
                std_lookup_result.unwrap().z_in_monomial.as_ref(),
                z,
            ))?;
            plookup_proof.opening_proof =
                commit_using_monomials(&quotient_of_lookup_z, &crs_mon, &worker)?;
        }

        multiopening_challenge.mul_assign(&v);

        let mut poly_to_divide_at_z_omega = z_in_monomial_form;
        poly_to_divide_at_z_omega.scale(&worker, multiopening_challenge);

        multiopening_challenge.mul_assign(&v);

        // d should be opened at z*omega due to d_next
        poly_to_divide_at_z_omega.add_assign_scaled(
            &worker,
            &witness_polys_in_monomial_form[3],
            &multiopening_challenge,
        );
        drop(witness_polys_in_monomial_form);

        debug_assert_eq!(multiopening_challenge, v.pow(&[(1 + 4 + 3 + 1 + 1) as u64]));

        // division in monomial form is sequential, so we parallelize the divisions

        let mut polys = vec![
            (poly_to_divide_at_z, z),
            (poly_to_divide_at_z_omega, z_by_omega),
        ];

        worker.scope(polys.len(), |scope, chunk| {
            for p in polys.chunks_mut(chunk) {
                scope.spawn(move |_| {
                    let (poly, at) = &p[0];
                    let at = *at;
                    let result = divide_single::<E>(poly.as_ref(), at);
                    p[0] = (Polynomial::from_coeffs(result).unwrap(), at);
                });
            }
        });

        let open_at_z_omega = polys.pop().unwrap().0;
        let open_at_z = polys.pop().unwrap().0;

        let opening_at_z = commit_using_monomials(&open_at_z, &crs_mon, &worker)?;

        let opening_at_z_omega = commit_using_monomials(&open_at_z_omega, &crs_mon, &worker)?;

        proof.opening_at_z_proof = opening_at_z;
        proof.opening_at_z_omega_proof = opening_at_z_omega;

        Ok(proof)
    }
}

#[cfg(test)]
mod test {
    use super::super::verifier::verify;
    use super::*;

    use crate::pairing::Engine;

    #[derive(Clone)]
    struct TestCircuit4<E: Engine> {
        _marker: PhantomData<E>,
    }

    impl<E: Engine> Circuit<E, PlonkCsWidth4WithNextStepParams> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E, PlonkCsWidth4WithNextStepParams>>(
            &self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let zero = E::Fr::zero();
            let one = E::Fr::one();
            let mut neg_one = E::Fr::one();
            neg_one.negate();

            let count = 2;
            for i in 0..count {
                for j in 0..count {
                    let left_val = E::Fr::from_str(&j.to_string()).unwrap();
                    let right_val = E::Fr::from_str(&i.to_string()).unwrap();

                    let left = cs.alloc(|| Ok(left_val))?;

                    let right = cs.alloc(|| Ok(right_val))?;

                    // lookup gate
                    let xor_result = cs.read_from_table(TableType::XOR, left, right)?;
                    let xor_result_val = cs.get_value(xor_result)?;

                    let and_result = cs.read_from_table(TableType::AND, left, right)?;
                    let and_result_val = cs.get_value(and_result)?;

                    let add = cs.alloc(|| {
                        let mut sum = left_val.clone();
                        // sum.add_assign(&right_val);
                        sum.add_assign(&xor_result_val);
                        sum.add_assign(&and_result_val);
                        Ok(sum)
                    })?;

                    cs.new_gate(
                        // [left, right, xor_result, add],
                        [left, xor_result, and_result, add],
                        [one, one, one, neg_one, zero, zero, zero, zero, zero],
                        [zero],
                    )?;

                    // range lookup
                    let range_val = E::Fr::from_str(&format!("{}", 2)).unwrap();
                    let range_var = cs.alloc(|| Ok(range_val))?;
                    let range_result =
                        cs.read_from_table(TableType::Range, range_var, cs.get_dummy_variable())?;

                    cs.new_gate(
                        [
                            range_result,
                            cs.get_dummy_variable(),
                            cs.get_dummy_variable(),
                            range_result,
                        ],
                        [one, one, one, neg_one, zero, zero, zero, zero, zero],
                        [zero],
                    )?;
                }
            }

            Ok(())
        }
    }

    #[test]
    fn test_plookup_prover() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::plookup::generator::*;
        use crate::plonk::plookup::keys::*;
        use crate::plonk::plookup::lookup_table::{AndTable, RangeTable, XorTable};
        use crate::worker::Worker;

        let bit_size = 2;

        let xor_table = XorTable::<Fr>::new(bit_size);
        let and_table = AndTable::<Fr>::new(bit_size);
        let range_table = RangeTable::new(1 << 4);

        let mut lookup_tables = Vec::<Box<dyn LookupTable<Fr>>>::new();
        lookup_tables.push(Box::new(xor_table));
        lookup_tables.push(Box::new(and_table));
        lookup_tables.push(Box::new(range_table));

        let mut assembly =
            GeneratorAssembly4WithNextStep::<Bn256>::new_with_lookup_tables(&lookup_tables);

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData,
        };

        circuit
            .clone()
            .synthesize(&mut assembly)
            .expect("must work");

        assembly.finalize();

        let worker = Worker::new();
        // let worker = Worker::new_with_cpus(4);

        let setup = assembly.setup(&worker).unwrap();

        let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(
            setup.permutation_polynomials[0].size(),
            &worker,
        );
        let crs_vals = Crs::<Bn256, CrsForLagrangeForm>::crs_42(
            setup.permutation_polynomials[0].size(),
            &worker,
        );

        let verification_key = VerificationKey::from_setup(&setup, &worker, &crs_mons).unwrap();

        let precomputations = SetupPolynomialsPrecomputations::from_setup(&setup, &worker).unwrap();

        // we use lookup gates in lookup tables so it needs to be mutable
        let mut assembly =
            ProverAssembly4WithNextStep::<Bn256>::new_with_lookup_tables(&mut lookup_tables);

        circuit
            .clone()
            .synthesize(&mut assembly)
            .expect("must work");

        assembly.finalize();

        let size = setup.permutation_polynomials[0].size();

        type Transcr = Blake2sTranscript<Fr>;

        let omegas_bitreversed =
            BitReversedOmegas::<Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed =
            <OmegasInvBitreversed<Fr> as CTPrecomputations<Fr>>::new_for_domain_size(
                size.next_power_of_two(),
            );

        let proof = assembly
            .prove::<Transcr, _, _>(
                &worker,
                &setup,
                &precomputations,
                &crs_vals,
                &crs_mons,
                &omegas_bitreversed,
                &omegas_inv_bitreversed,
            )
            .unwrap();

        let is_valid =
            verify::<Bn256, PlonkCsWidth4WithNextStepParams, Transcr>(&proof, &verification_key)
                .unwrap();

        assert!(is_valid);

        assert!(Fr::zero() < Fr::one());
    }
}
