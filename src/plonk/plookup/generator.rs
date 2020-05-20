use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::Engine;

use crate::plonk::domains::*;
use crate::plonk::polynomials::*;
use crate::worker::Worker;
use crate::SynthesisError;

use std::marker::PhantomData;

use super::cs::*;
use super::keys::SetupPolynomials;
use super::lookup_table::{LookupTable, RangeTable, TableType};
use super::utils::make_non_residues;

// #[derive(Debug)]
pub struct GeneratorAssembly<'a, E: Engine, P: PlonkConstraintSystemParams<E>> {
    m: usize,
    n: usize,
    input_gates: Vec<(
        P::StateVariables,
        P::ThisTraceStepCoefficients,
        P::NextTraceStepCoefficients,
    )>,
    aux_gates: Vec<(
        P::StateVariables,
        P::ThisTraceStepCoefficients,
        P::NextTraceStepCoefficients,
    )>,

    num_inputs: usize,
    num_aux: usize,
    num_standard_lookups: usize,
    num_range_lookups: usize,

    lookup_tables: &'a [Box<dyn LookupTable<E::Fr>>],
    is_table_initialized: bool,

    inputs_map: Vec<usize>,

    is_finalized: bool,
}

impl<'a, E: Engine, P: PlonkConstraintSystemParams<E>> ConstraintSystem<E, P>
    for GeneratorAssembly<'a, E, P>
{
    // allocate a variable
    fn alloc<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        self.num_aux += 1;
        let index = self.num_aux;

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        self.num_inputs += 1;
        let index = self.num_inputs;

        let input_var = Variable(Index::Input(index));

        let dummy = self.get_dummy_variable();

        let vars = P::StateVariables::from_variable_and_padding(input_var, dummy);
        let mut this_step_coeffs = P::ThisTraceStepCoefficients::identity();
        this_step_coeffs.negate(); // we use -1 here to later add to the constants polynomial using + sign
        let next_step_coeffs = P::NextTraceStepCoefficients::empty();

        self.input_gates
            .push((vars, this_step_coeffs, next_step_coeffs));
        self.n += 1;

        Ok(input_var)
    }

    // allocate an abstract gate
    fn new_gate(
        &mut self,
        variables: P::StateVariables,
        this_step_coeffs: P::ThisTraceStepCoefficients,
        next_step_coeffs: P::NextTraceStepCoefficients,
    ) -> Result<(), SynthesisError> {
        self.aux_gates
            .push((variables, this_step_coeffs, next_step_coeffs));
        self.n += 1;

        Ok(())
    }

    fn get_value(&self, _var: Variable) -> Result<E::Fr, SynthesisError> {
        // Err(SynthesisError::AssignmentMissing) // @TODO: ask Alex
        Ok(E::Fr::zero())
    }

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }

    fn read_from_table(
        &mut self,
        table_type: TableType,
        _a: Variable,
        _b: Variable,
    ) -> Result<Variable, SynthesisError> {
        assert!(self.is_table_initialized);

        let mut lookup_table_type_as_fe = E::Fr::zero();
        let mut is_table_found = false;

        // rewrite this ugly for loop
        for t in self.lookup_tables.iter() {
            if table_type.to_string() == t.lookup_type().to_string() {
                lookup_table_type_as_fe = t.lookup_table_type_as_fe();
                is_table_found = true;
                break;
            }
        }
        if !is_table_found {
            return Err(SynthesisError::Unsatisfiable);
        }

        let variables = P::StateVariables::from_variables(&vec![self.get_dummy_variable(); 4]);
        let mut coeffs = vec![E::Fr::zero(); 9];
        match table_type {
            TableType::XOR | TableType::AND => {
                coeffs[6] = E::Fr::one();
                self.num_standard_lookups += 1
            }
            TableType::Range => {
                coeffs[7] = E::Fr::one();
                self.num_range_lookups += 1
            }
            _ => (),
        }
        coeffs[8] = lookup_table_type_as_fe;
        let this_step_coeffs = P::ThisTraceStepCoefficients::from_coeffs(&coeffs);
        let next_step_coeffs = P::NextTraceStepCoefficients::empty();
        self.new_gate(variables, this_step_coeffs, next_step_coeffs)?;

        Ok(self.get_dummy_variable())
    }
}

impl<'a, E: Engine, P: PlonkConstraintSystemParams<E>> GeneratorAssembly<'a, E, P> {
    pub fn new() -> Self {
        let tmp = Self {
            n: 0,
            m: 0,
            input_gates: vec![],
            aux_gates: vec![],

            num_inputs: 0,
            num_aux: 0,
            num_standard_lookups: 0,
            num_range_lookups: 0,

            lookup_tables: &[],
            is_table_initialized: false,

            inputs_map: vec![],

            is_finalized: false,
        };

        tmp
    }

    pub fn new_with_size_hints(num_inputs: usize, num_aux: usize) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,
            input_gates: Vec::with_capacity(num_inputs),
            aux_gates: Vec::with_capacity(num_aux),

            num_inputs: 0,
            num_aux: 0,
            num_standard_lookups: 0,
            num_range_lookups: 0,

            lookup_tables: &[],
            is_table_initialized: false,

            inputs_map: Vec::with_capacity(num_inputs),

            is_finalized: false,
        };

        tmp
    }

    pub fn new_with_lookup_tables(lookup_tables: &'a [Box<dyn LookupTable<E::Fr>>]) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,
            input_gates: vec![],
            aux_gates: vec![],

            num_inputs: 0,
            num_aux: 0,
            num_standard_lookups: 0,
            num_range_lookups: 0,

            lookup_tables: lookup_tables,

            is_table_initialized: true,

            inputs_map: vec![],

            is_finalized: false,
        };

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn num_gates(&self) -> usize {
        self.input_gates.len() + self.aux_gates.len()
    }

    pub fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }
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

        println!("generator gates {}", self.n);

        self.is_finalized = true;
    }
}

// later we can alias traits
// pub trait PlonkCsWidth3WithNextStep<E: Engine> = ConstraintSystem<E, PlonkCsWidth3WithNextStepParams>;

pub type GeneratorAssembly3WithNextStep<'a, E> =
    GeneratorAssembly<'a, E, PlonkCsWidth3WithNextStepParams>;
pub type GeneratorAssembly4WithNextStep<'a, E> =
    GeneratorAssembly<'a, E, PlonkCsWidth4WithNextStepParams>;

impl<'a, E: Engine> GeneratorAssembly4WithNextStep<'a, E> {
    pub fn make_selector_polynomials(
        &self,
        worker: &Worker,
    ) -> Result<
        (
            [Polynomial<E::Fr, Values>; 9],
            [Polynomial<E::Fr, Values>; 1],
        ),
        SynthesisError,
    > {
        assert!(self.is_finalized);
        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut q_a = vec![E::Fr::zero(); total_num_gates];
        let mut q_b = vec![E::Fr::zero(); total_num_gates];
        let mut q_c = vec![E::Fr::zero(); total_num_gates];
        let mut q_d = vec![E::Fr::zero(); total_num_gates];
        let mut q_m = vec![E::Fr::zero(); total_num_gates];
        let mut q_const = vec![E::Fr::zero(); total_num_gates];
        let mut q_lookup = vec![E::Fr::zero(); total_num_gates];
        let mut q_range = vec![E::Fr::zero(); total_num_gates];
        let mut q_table_index = vec![E::Fr::zero(); total_num_gates];

        let mut q_d_next = vec![E::Fr::zero(); total_num_gates];

        // expect a small number of inputs
        for (gate, q_a) in self.input_gates.iter().zip(q_a.iter_mut()) {
            let mut tmp = gate.1[0];
            tmp.negate();
            // -a + const = 0, where const will come from verifier
            assert_eq!(tmp, E::Fr::one());
            *q_a = gate.1[0];
        }

        // now fill the aux gates

        let num_input_gates = self.input_gates.len();
        let q_a_aux = &mut q_a[num_input_gates..];
        let q_b_aux = &mut q_b[num_input_gates..];
        let q_c_aux = &mut q_c[num_input_gates..];
        let q_d_aux = &mut q_d[num_input_gates..];
        let q_m_aux = &mut q_m[num_input_gates..];
        let q_const_aux = &mut q_const[num_input_gates..];
        let q_lookup_aux = &mut q_lookup[num_input_gates..];
        let q_range_aux = &mut q_range[num_input_gates..];
        let q_table_index_aux = &mut q_table_index[num_input_gates..];

        let q_d_next_aux = &mut q_d_next[num_input_gates..];

        debug_assert!(self.aux_gates.len() == q_a_aux.len());

        worker.scope(self.aux_gates.len(), |scope, chunk| {
            for (
                (
                    ((((((((gate, q_a), q_b), q_c), q_d), q_m), q_const), q_lookup), q_range),
                    q_table_index,
                ),
                q_d_next,
            ) in self
                .aux_gates
                .chunks(chunk)
                .zip(q_a_aux.chunks_mut(chunk))
                .zip(q_b_aux.chunks_mut(chunk))
                .zip(q_c_aux.chunks_mut(chunk))
                .zip(q_d_aux.chunks_mut(chunk))
                .zip(q_m_aux.chunks_mut(chunk))
                .zip(q_const_aux.chunks_mut(chunk))
                .zip(q_lookup_aux.chunks_mut(chunk))
                .zip(q_range_aux.chunks_mut(chunk))
                .zip(q_table_index_aux.chunks_mut(chunk))
                .zip(q_d_next_aux.chunks_mut(chunk))
            {
                scope.spawn(move |_| {
                    for (
                        (
                            (
                                (((((((gate, q_a), q_b), q_c), q_d), q_m), q_const), q_lookup),
                                q_range,
                            ),
                            q_table_index,
                        ),
                        q_d_next,
                    ) in gate
                        .iter()
                        .zip(q_a.iter_mut())
                        .zip(q_b.iter_mut())
                        .zip(q_c.iter_mut())
                        .zip(q_d.iter_mut())
                        .zip(q_m.iter_mut())
                        .zip(q_const.iter_mut())
                        .zip(q_lookup.iter_mut())
                        .zip(q_range.iter_mut())
                        .zip(q_table_index.iter_mut())
                        .zip(q_d_next.iter_mut())
                    {
                        *q_a = gate.1[0];
                        *q_b = gate.1[1];
                        *q_c = gate.1[2];
                        *q_d = gate.1[3];
                        *q_m = gate.1[4];
                        *q_const = gate.1[5];
                        *q_lookup = gate.1[6];
                        *q_range = gate.1[7];
                        *q_table_index = gate.1[8];

                        *q_d_next = gate.2[0];
                    }
                });
            }
        });

        let q_a = Polynomial::from_values(q_a)?;
        let q_b = Polynomial::from_values(q_b)?;
        let q_c = Polynomial::from_values(q_c)?;
        let q_d = Polynomial::from_values(q_d)?;
        let q_m = Polynomial::from_values(q_m)?;
        let q_const = Polynomial::from_values(q_const)?;
        let q_lookup = Polynomial::from_values(q_lookup)?;
        let q_range = Polynomial::from_values(q_range)?;
        let q_table_index = Polynomial::from_values(q_table_index)?;
        // println!("range polys");
        // q_range.as_ref().iter().for_each(|e| println!("{}", e));

        let q_d_next = Polynomial::from_values(q_d_next)?;

        Ok((
            [
                q_a,
                q_b,
                q_c,
                q_d,
                q_m,
                q_const,
                q_lookup,
                q_range,
                q_table_index,
            ],
            [q_d_next],
        ))
    }

    pub(crate) fn make_permutations(&self, worker: &Worker) -> [Polynomial<E::Fr, Values>; 4] {
        assert!(self.is_finalized);

        let num_gates = self.input_gates.len() + self.aux_gates.len();
        let num_partitions = self.num_inputs + self.num_aux;
        let num_inputs = self.num_inputs;
        // in the partition number i there is a set of indexes in V = (a, b, c) such that V_j = i
        let mut partitions = vec![vec![]; num_partitions + 1];

        // gate_idx is zero-enumerated here
        for (gate_idx, (vars, _, _)) in self.input_gates.iter().chain(&self.aux_gates).enumerate() {
            for (var_index_in_gate, v) in vars.iter().enumerate() {
                match v {
                    Variable(Index::Aux(0)) => {
                        // Dummy variables do not participate in the permutation
                    }
                    Variable(Index::Input(0)) => {
                        unreachable!("There must be no input with index 0");
                    }
                    Variable(Index::Input(index)) => {
                        let i = *index; // inputs are [1, num_inputs]
                        partitions[i].push((var_index_in_gate, gate_idx + 1));
                    }
                    Variable(Index::Aux(index)) => {
                        let i = index + num_inputs; // aux are [num_inputs + 1, ..]
                        partitions[i].push((var_index_in_gate, gate_idx + 1));
                    }
                }
            }
        }

        // sanity check
        assert_eq!(partitions[0].len(), 0);

        let domain = Domain::new_for_size(num_gates as u64)
            .expect("must have enough roots of unity to fit the circuit");

        // now we need to make root at it's cosets
        let domain_elements =
            materialize_domain_elements_with_natural_enumeration(&domain, &worker);

        // domain_elements.pop().unwrap();

        use crate::ff::LegendreSymbol;
        use crate::ff::SqrtField;

        let mut non_residues = vec![];
        non_residues.push(E::Fr::one());
        non_residues.extend(make_non_residues::<E::Fr>(3, &domain));

        assert_eq!(non_residues.len(), 4);

        let mut sigma_1 = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
        sigma_1.scale(&worker, non_residues[0]);
        let mut sigma_2 = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
        sigma_2.scale(&worker, non_residues[1]);
        let mut sigma_3 = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
        sigma_3.scale(&worker, non_residues[2]);
        let mut sigma_4 = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
        sigma_4.scale(&worker, non_residues[3]);

        let mut permutations = vec![vec![]; num_partitions + 1];

        fn rotate<T: Sized>(mut vec: Vec<T>) -> Vec<T> {
            if vec.len() > 1 {
                let mut els: Vec<_> = vec.drain(0..1).collect();
                els.reverse();
                vec.push(els.pop().unwrap());
            }

            vec
        }

        for (i, partition) in partitions.into_iter().enumerate().skip(1) {
            // copy-permutation should have a cycle around the partition

            // we do not need to permute over partitions of length 1,
            // as this variable only happends in one place
            if partition.len() == 1 {
                continue;
            }

            let permutation = rotate(partition.clone());
            permutations[i] = permutation.clone();

            // let permutation = partition.clone();
            // permutations[i] = permutation;

            for (original, new) in partition.into_iter().zip(permutation.into_iter()) {
                // (column_idx, trace_step_idx)
                let new_zero_enumerated = new.1 - 1;
                let mut new_value = domain_elements[new_zero_enumerated];

                // we have shuffled the values, so we need to determine FROM
                // which of k_i * {1, omega, ...} cosets we take a value
                // for a permutation polynomial
                new_value.mul_assign(&non_residues[new.0]);

                // check to what witness polynomial the variable belongs
                let place_into = match original.0 {
                    0 => sigma_1.as_mut(),
                    1 => sigma_2.as_mut(),
                    2 => sigma_3.as_mut(),
                    3 => sigma_4.as_mut(),
                    _ => unreachable!(),
                };

                let original_zero_enumerated = original.1 - 1;
                place_into[original_zero_enumerated] = new_value;
            }
        }

        // sigma_1.pad_to_domain().expect("must pad to power of two");
        // sigma_2.pad_to_domain().expect("must pad to power of two");
        // sigma_3.pad_to_domain().expect("must pad to power of two");
        // sigma_4.pad_to_domain().expect("must pad to power of two");

        [sigma_1, sigma_2, sigma_3, sigma_4]
    }

    pub fn make_lookup_table_polynomials(
        &self,
    ) -> Result<Vec<Polynomial<E::Fr, Values>>, SynthesisError> {
        assert!(self.is_table_initialized);

        let mut total_row_count = 0;

        let standard_lookup_tables = self
            .lookup_tables
            .iter()
            .filter(|t| t.lookup_type() != TableType::Range);

        for lookup_table in standard_lookup_tables.clone() {
            total_row_count += lookup_table.size();
        }

        // prepend zeroes
        let mut t1_values = vec![E::Fr::zero(); self.n - total_row_count];
        let mut t2_values = vec![E::Fr::zero(); self.n - total_row_count];
        let mut t3_values = vec![E::Fr::zero(); self.n - total_row_count];
        let mut t4_values = vec![E::Fr::zero(); self.n - total_row_count];

        for lookup_table in standard_lookup_tables {
            assert_ne!(
                lookup_table.lookup_type().to_string(),
                TableType::Range.to_string()
            );
            for row in lookup_table.iter() {
                t1_values.push(row.0);
                t2_values.push(row.1);
                t3_values.push(row.2);
                t4_values.push(lookup_table.lookup_table_type_as_fe());
            }
        }

        let t1 = Polynomial::from_values_unpadded(t1_values)?;
        let t2 = Polynomial::from_values_unpadded(t2_values)?;
        let t3 = Polynomial::from_values_unpadded(t3_values)?;
        let t4 = Polynomial::from_values_unpadded(t4_values)?;

        Ok(vec![t1, t2, t3, t4])
    }

    pub fn make_range_lookup_table_polynomials(
        &self,
    ) -> Result<Vec<Polynomial<E::Fr, Values>>, SynthesisError> {
        assert!(self.is_table_initialized);

        let mut total_row_count = 0;

        let range_lookup_tables = self
            .lookup_tables
            .iter()
            .filter(|t| t.lookup_type() == TableType::Range);

        for lookup_table in range_lookup_tables.clone() {
            total_row_count += lookup_table.size();
        }

        // prepend zeroes
        let mut t1_values = vec![E::Fr::zero(); self.n - total_row_count];
        let mut t2_values = vec![E::Fr::zero(); self.n - total_row_count];
        let mut t3_values = vec![E::Fr::zero(); self.n - total_row_count];
        let mut t4_values = vec![E::Fr::zero(); self.n - total_row_count];

        for lookup_table in range_lookup_tables {
            assert_eq!(
                lookup_table.lookup_type().to_string(),
                TableType::Range.to_string()
            );
            for row in lookup_table.iter() {
                t1_values.push(row.0);
                t2_values.push(row.1);
                t3_values.push(row.2);
                t4_values.push(lookup_table.lookup_table_type_as_fe());
            }
        }

        let t1 = Polynomial::from_values_unpadded(t1_values)?;
        let t2 = Polynomial::from_values_unpadded(t2_values)?;
        let t3 = Polynomial::from_values_unpadded(t3_values)?;
        let t4 = Polynomial::from_values_unpadded(t4_values)?;

        Ok(vec![t1, t2, t3, t4])
    }

    pub fn setup(
        self,
        worker: &Worker,
    ) -> Result<SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
        assert!(self.is_finalized);

        let n = self.n;
        let num_inputs = self.num_inputs;

        let [sigma_1, sigma_2, sigma_3, sigma_4] = self.make_permutations(&worker);

        let ([q_a, q_b, q_c, q_d, q_m, q_const, q_lookup, q_range, q_table_index], [q_d_next]) =
            self.make_selector_polynomials(&worker)?;

        let standard_lookup_table_polynomials = self.make_lookup_table_polynomials()?;
        let range_lookup_table_polynomials = self.make_range_lookup_table_polynomials()?;

        drop(self);

        let sigma_1 = sigma_1.ifft(&worker);
        let sigma_2 = sigma_2.ifft(&worker);
        let sigma_3 = sigma_3.ifft(&worker);
        let sigma_4 = sigma_4.ifft(&worker);

        let q_a = q_a.ifft(&worker);
        let q_b = q_b.ifft(&worker);
        let q_c = q_c.ifft(&worker);
        let q_d = q_d.ifft(&worker);
        let q_m = q_m.ifft(&worker);
        let q_const = q_const.ifft(&worker);
        let q_lookup = q_lookup.ifft(&worker);
        let q_range = q_range.ifft(&worker); // TODO: do wee need to monomials?
        let q_table_index = q_table_index.ifft(&worker);

        let q_d_next = q_d_next.ifft(&worker);

        let setup = SetupPolynomials::<E, PlonkCsWidth4WithNextStepParams> {
            n,
            num_inputs,
            selector_polynomials: vec![
                q_a,
                q_b,
                q_c,
                q_d,
                q_m,
                q_const,
                q_lookup,
                q_range,
                q_table_index,
            ],
            next_step_selector_polynomials: vec![q_d_next],
            permutation_polynomials: vec![sigma_1, sigma_2, sigma_3, sigma_4],

            lookup_table_polynomials: standard_lookup_table_polynomials,
            range_table_polynomials: range_lookup_table_polynomials,

            _marker: std::marker::PhantomData,
        };

        Ok(setup)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::pairing::Engine;

    struct TestCircuit4<E: Engine> {
        _marker: PhantomData<E>,
    }

    impl<E: Engine> Circuit<E, PlonkCsWidth4WithNextStepParams> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E, PlonkCsWidth4WithNextStepParams>>(
            &self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| Ok(E::Fr::from_str("10").unwrap()))?;

            println!("A = {:?}", a);

            let b = cs.alloc(|| Ok(E::Fr::from_str("20").unwrap()))?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| Ok(E::Fr::from_str("200").unwrap()))?;

            println!("C = {:?}", c);

            let d = cs.alloc(|| Ok(E::Fr::from_str("100").unwrap()))?;

            println!("D = {:?}", d);

            let zero = E::Fr::zero();

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            let dummy = cs.get_dummy_variable();

            // 2a - b == 0
            cs.new_gate(
                [a, b, dummy, dummy],
                [two, negative_one, zero, zero, zero, zero, zero, zero, zero],
                [zero],
            )?;

            // 10b - c = 0
            let ten = E::Fr::from_str("10").unwrap();

            cs.new_gate(
                [b, c, dummy, dummy],
                [ten, negative_one, zero, zero, zero, zero, zero, zero, zero],
                [zero],
            )?;

            // c - a*b == 0

            cs.new_gate(
                [a, b, dummy, c],
                [zero, zero, zero, negative_one, one, zero, zero, zero, zero],
                [zero],
            )?;

            // 10a + 10b - c - d == 0

            cs.new_gate(
                [a, b, c, d],
                [
                    ten,
                    ten,
                    negative_one,
                    negative_one,
                    zero,
                    zero,
                    zero,
                    zero,
                    zero,
                ],
                [zero],
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_trivial_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::plookup::lookup_table::XorTable;
        use crate::worker::Worker;

        let mut assembly = GeneratorAssembly4WithNextStep::<Bn256>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData,
        };

        circuit.synthesize(&mut assembly).expect("must work");

        // println!("{:?}", assembly);

        assembly.finalize();

        let worker = Worker::new();

        println!("Char = {}", Fr::char());

        let [sigma_1, sigma_2, sigma_3, sigma_4] = assembly.make_permutations(&worker);

        let zero = Fr::zero();

        let a_var_value = Fr::from_str("10").unwrap();
        let b_var_value = Fr::from_str("20").unwrap();
        let c_var_value = Fr::from_str("200").unwrap();
        let d_var_value = Fr::from_str("100").unwrap();

        let dummy_1 = Fr::from_str("123").unwrap();
        let dummy_2 = Fr::from_str("456").unwrap();

        let a = vec![
            a_var_value,
            b_var_value,
            a_var_value,
            a_var_value,
            zero,
            zero,
            zero,
        ];
        let b = vec![
            b_var_value,
            c_var_value,
            b_var_value,
            b_var_value,
            zero,
            zero,
            zero,
        ];
        let c = vec![dummy_1, zero, zero, c_var_value, zero, zero, zero];
        let d = vec![zero, dummy_2, c_var_value, d_var_value, zero, zero, zero];

        let num_gates = assembly.num_gates();

        let beta = Fr::from_str("15").unwrap();
        let gamma = Fr::from_str("4").unwrap();

        let domain = crate::plonk::domains::Domain::new_for_size(num_gates as u64).unwrap();
        let omega = domain.generator;

        let mut non_res = vec![Fr::one()];
        non_res.extend(make_non_residues::<Fr>(3, &domain));

        let p = vec![
            (a, sigma_1, non_res[0]),
            (b, sigma_2, non_res[1]),
            (c, sigma_3, non_res[2]),
            (d, sigma_4, non_res[3]),
        ];

        let mut subproducts: Vec<Vec<Fr>> = vec![vec![]; 4];
        let mut permuted_subproducts: Vec<Vec<Fr>> = vec![vec![]; 4];

        for (((wit, perm, non_res), subprod), permuted_subprod) in p
            .into_iter()
            .zip(subproducts.iter_mut())
            .zip(permuted_subproducts.iter_mut())
        {
            let mut current = non_res; // omega^0 * k
            for (el, sig) in wit.iter().zip(perm.as_ref().iter()) {
                let mut tmp = current;
                tmp.mul_assign(&beta);
                tmp.add_assign(&gamma);
                tmp.add_assign(&el);
                subprod.push(tmp);

                let mut tmp = *sig;
                tmp.mul_assign(&beta);
                tmp.add_assign(&gamma);
                tmp.add_assign(&el);
                permuted_subprod.push(tmp);

                current.mul_assign(&omega);
            }
        }

        let mut f_poly = vec![];
        let mut g_poly = vec![];

        for i in 0..subproducts[0].len() {
            let mut tmp = Fr::one();
            for p in subproducts.iter() {
                tmp.mul_assign(&p[i]);
            }

            f_poly.push(tmp);
        }

        for i in 0..permuted_subproducts[0].len() {
            let mut tmp = Fr::one();
            for p in permuted_subproducts.iter() {
                tmp.mul_assign(&p[i]);
            }

            g_poly.push(tmp);
        }

        let mut tmp = Fr::one();
        let mut f_prime = vec![tmp];
        for el in f_poly.iter() {
            tmp.mul_assign(&el);
            f_prime.push(tmp);
        }

        let mut tmp = Fr::one();
        let mut g_prime = vec![tmp];
        for el in g_poly.iter() {
            tmp.mul_assign(&el);
            g_prime.push(tmp);
        }

        assert!(f_prime[0] == g_prime[0]);
        assert!(f_prime[num_gates] == g_prime[num_gates]);

        let _setup = assembly.setup(&worker).unwrap();
    }
}
