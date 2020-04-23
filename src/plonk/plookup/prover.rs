use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use crate::plonk::polynomials::*;
use crate::worker::Worker;
use crate::plonk::domains::*;

use std::marker::PhantomData;

use super::cs::*;
use super::keys::{SetupPolynomials, Proof, SetupPolynomialsPrecomputations};

use crate::source::{DensityTracker, DensityTrackerersChain};

use crate::kate_commitment::*;
use super::utils::*;

use crate::plonk::commitments::transcript::*;
use crate::plonk::fft::cooley_tukey_ntt::*;

use super::LDE_FACTOR;

// #[derive(Debug, Clone)]
pub struct ProverAssembly<E: Engine, P: PlonkConstraintSystemParams<E>> {
    m: usize,
    n: usize,
    // input_gates: Vec<(P::StateVariables, P::ThisTraceStepCoefficients, P::NextTraceStepCoefficients)>,
    // aux_gates: Vec<(P::StateVariables, P::ThisTraceStepCoefficients, P::NextTraceStepCoefficients)>,

    num_inputs: usize,
    num_aux: usize,
    num_lookups: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    wire_assignments: Vec<Vec<E::Fr>>,

    // aux_densities: Vec<DensityTracker>,

    inputs_map: Vec<usize>,
    dummy_var: Variable,

    is_finalized: bool,

    lookup_table: Vec<(E::Fr, E::Fr, E::Fr)>,
    is_table_initialized: bool,

    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>> ConstraintSystem<E, P> for ProverAssembly<E, P> {
    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
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
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
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
    fn new_gate(&mut self, 
        variables: P::StateVariables, 
        _this_step_coeffs: P::ThisTraceStepCoefficients,
        _next_step_coeffs: P::NextTraceStepCoefficients
    ) -> Result<(), SynthesisError>
    {
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
            Variable(Index::Input(input)) => {
                self.input_assingments[input - 1]
            },
            Variable(Index::Aux(aux)) => {
                self.aux_assingments[aux - 1]
            }
        };

        Ok(value)
    }

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }

    fn read_from_table(&mut self, a: Variable, b: Variable) -> Result<Variable, SynthesisError>{
        let a_val = self.get_value(a)?;
        let b_val = self.get_value(b)?;
        let c_val = self.find_value_in_table(a_val, b_val)?;
        
        let c = self.alloc(|| {
            Ok(c_val)
        })?;

        self.wire_assignments[0].push(a_val);
        self.wire_assignments[1].push(b_val);
        self.wire_assignments[2].push(c_val);
        self.wire_assignments[3].push(E::Fr::zero());
        // println!("n {}", self.n);
        self.n += 1;
        self.num_lookups += 1;
        Ok(c)
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>> ProverAssembly<E, P> {
    pub fn new() -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,
            num_lookups: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            wire_assignments: vec![vec![]; P::STATE_WIDTH],
        
            // aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],

            inputs_map: vec![],
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            lookup_table: vec![],
            is_table_initialized: false,

            _marker: std::marker::PhantomData
        };

        tmp
    }

    pub fn new_with_size_hints(num_inputs: usize, num_aux: usize) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,
            num_lookups: 0,

            input_assingments: Vec::with_capacity(num_inputs),
            aux_assingments: Vec::with_capacity(num_aux),

            wire_assignments: vec![Vec::with_capacity(num_inputs + num_aux); P::STATE_WIDTH],
        
            // aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],

            inputs_map: Vec::with_capacity(num_inputs),
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            lookup_table: vec![],
            is_table_initialized: false,

            _marker: std::marker::PhantomData
        };

        tmp
    }
    
    pub fn new_with_lookup_table(table: Vec<(E::Fr, E::Fr, E::Fr)>) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,
            num_inputs: 0,
            num_aux: 0,
            num_lookups: 0,
            input_assingments: vec![],
            aux_assingments: vec![],
            wire_assignments: vec![vec![]; P::STATE_WIDTH],
            inputs_map: vec![],
            dummy_var: Variable(Index::Aux(0)),
            is_finalized: false,
            lookup_table: table,
            is_table_initialized: true,

            _marker: std::marker::PhantomData
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
        let table_size = self.lookup_table.len();
        let lookup_gates = self.num_lookups;
        let filled_gates = self.n + self.num_inputs;
        let n = filled_gates.max(table_size + lookup_gates);

        if (n+1).is_power_of_two() {
            self.is_finalized = true;
            return;
        }

        for _ in (self.n+1)..(n+1).next_power_of_two(){
            let variables = P::StateVariables::from_variables(&vec![self.get_dummy_variable();4]);            
            self.new_gate(
                variables, 
                P::ThisTraceStepCoefficients::empty(), 
                P::NextTraceStepCoefficients::empty(),
            ).unwrap(); // TODO: change func signature to handle Result?
        }

        self.is_finalized = true;
    }

    pub fn find_value_in_table(&self, a: E::Fr, b: E::Fr) -> Result<E::Fr, SynthesisError>{        
        // TODO: c =
        let (_, _, c) = self.lookup_table.iter().find(|(col1, col2, _)| (*col1 == a && *col2 == b ) || (*col1 == b && *col2 == a ) ).expect("table must have");

        Ok(*c)
    }

    pub fn get_lookup_table(self) -> Vec<(E::Fr, E::Fr, E::Fr)>{
        self.lookup_table
    }
    pub fn make_witness_polynomials(
        self
    ) -> Result<Vec<Vec<E::Fr>>, SynthesisError>
    {
        assert!(self.is_finalized);

        let mut full_assignments = vec![Vec::with_capacity((self.n+1).next_power_of_two()); self.wire_assignments.len()];

        for inp in self.input_assingments.into_iter() {
            // inputs will always go into A wire
            full_assignments[0].push(inp);
            for i in 1..full_assignments.len() {
                full_assignments[i].push(E::Fr::zero());
            }
        }

        for (idx, aux) in self.wire_assignments.into_iter().enumerate() {
            full_assignments[idx].extend(aux);
            full_assignments[idx].resize((self.n+1).next_power_of_two() - 1, E::Fr::zero());
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), (self.n+1).next_power_of_two() - 1);
        }

        Ok(full_assignments)
    }
}

use std::cmp::Ordering;
#[derive(Debug, Clone)]
pub struct MultiSet<E: Engine>([E::Fr; 3]);
impl<E: Engine> MultiSet<E>{
    pub fn new()-> Self{
        Self([E::Fr::zero();3])
    }
    pub fn from_vec(vec: [E::Fr;3])-> Self{
        Self(vec)
    }

    pub fn scale_and_sum(&self , s: E::Fr) -> E::Fr{
        let mut scalar = E::Fr::one();
        let mut sum = E::Fr::zero();

        self.0.iter().for_each(|e| {
            let mut tmp = e.clone();
            tmp.mul_assign(&scalar);
            sum.add_assign(&tmp);
            scalar.mul_assign(&s);
        }); 

        sum
    }
}

impl<E: Engine> PartialEq for MultiSet<E>{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0[0] == other.0[0] && self.0[1] == other.0[1] && self.0[2] == other.0[2]
    }
}

impl<E: Engine> Eq for MultiSet<E>{}

impl<E: Engine> PartialOrd for MultiSet<E>{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {       
        Some(self.cmp(other))
    }
}

impl<E: Engine> Ord for MultiSet<E>{
    fn cmp(&self, other: &Self) -> Ordering {
        let s0 = self.0[0].into_repr();
        let s1 = self.0[1].into_repr();
        let s2 = self.0[2].into_repr();
        
        let o0 = other.0[0].into_repr();
        let o1 = other.0[1].into_repr();
        let o2 = other.0[2].into_repr();

        if s1 == o1 {
            if s0 == o0 {
                if s2 < o2{
                    Ordering::Less
                }else{
                    Ordering::Greater
                }
            }else if s0 < o0 {
              Ordering::Less  
            }else{
                Ordering::Greater
            }
        }else if s1 < o1{
            Ordering::Less
        }else{
            Ordering::Greater
        }
    }
}

// later we can alias traits
// pub trait PlonkCsWidth3WithNextStep<E: Engine> = ConstraintSystem<E, PlonkCsWidth3WithNextStepParams>;

pub type ProverAssembly3WithNextStep<E> = ProverAssembly<E, PlonkCsWidth3WithNextStepParams>;
pub type ProverAssembly4WithNextStep<E> = ProverAssembly<E, PlonkCsWidth4WithNextStepParams>;

impl<E: Engine> ProverAssembly4WithNextStep<E> {
    pub fn prove<T: Transcript<E::Fr>, CP: CTPrecomputations<E::Fr>, CPI: CTPrecomputations<E::Fr>>(
        self, 
        worker: &Worker, 
        setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
        setup_precomputations: &SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>,
        crs_vals: &Crs<E, CrsForLagrangeForm>, 
        crs_mon: &Crs<E, CrsForMonomialForm>,
        omegas_bitreversed: &CP,
        omegas_inv_bitreversed: &CPI
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

        let lookup_table = self.lookup_table.clone();
        let num_lookup_gates = self.num_lookups;

        let full_assignments = self.make_witness_polynomials()?;

        let mut proof = Proof::<E, PlonkCsWidth4WithNextStepParams>::empty();
        proof.n = n;
        proof.num_inputs = num_inputs;
        proof.input_values = input_values.clone();

        let coset_factor = E::Fr::multiplicative_generator();

        // let coset_factor = E::Fr::one();

        // Commit wire polynomials 

        for wire_poly in full_assignments.iter() {
            let commitment = commit_using_raw_values(
                &wire_poly, 
                &crs_vals, 
                &worker
            )?;

            commit_point_as_xy::<E, _>(&mut transcript, &commitment);

            proof.wire_commitments.push(commitment);
        }

        // now transform assignments in the polynomials

        let mut assignment_polynomials = vec![];
        
        // @TODO:
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

        let mut domain_elements = materialize_domain_elements_with_natural_enumeration(
            &domain, 
            &worker
        );

        domain_elements.pop().expect("must pop last element for omega^i");

        let mut domain_elements_poly_by_beta = Polynomial::from_values_unpadded(domain_elements.clone())?;
        domain_elements_poly_by_beta.scale(&worker, beta);

        let non_residues = make_non_residues::<E::Fr>(
            <PlonkCsWidth4WithNextStepParams as PlonkConstraintSystemParams<E>>::STATE_WIDTH - 1, 
            &domain
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
                setup_precomputations.permutation_polynomials_values_of_size_n_minus_one.len(), 
                grand_products_protos_with_gamma.len()
            );
            let mut grand_products_proto_it = grand_products_protos_with_gamma.into_iter();
            let mut permutation_polys_it = setup_precomputations.permutation_polynomials_values_of_size_n_minus_one.iter();

            let mut z_2 = grand_products_proto_it.next().unwrap();
            z_2.add_assign_scaled(&worker, &permutation_polys_it.next().unwrap(), &beta);

            for (mut p, perm) in grand_products_proto_it
                                            .zip(permutation_polys_it) {
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

        let z_commitment = commit_using_values(
            &z, 
            &crs_vals, 
            &worker
        )?;
        proof.grand_product_commitment = z_commitment;

        commit_point_as_xy::<E, _>(&mut transcript, &proof.grand_product_commitment);

        // interpolate on the main domain
        let z_in_monomial_form = z.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // those are z(x*Omega) formally
        let mut z_shifted_in_monomial_form = z_in_monomial_form.clone();
        z_shifted_in_monomial_form.distribute_powers(&worker, z_in_monomial_form.omega);

        // z.clone().as_ref().iter().zip(z_shifted_in_monomial_form.clone().fft(&worker).as_ref().iter()).for_each(|(z, sz)| println!("{} {}", z, sz));
        
        // now we have to LDE everything and compute quotient polynomial
        // also to save on openings that we will have to do from the monomial form anyway

        let mut witness_polys_in_monomial_form = vec![];

        let mut witness_ldes_on_coset = vec![];
        let mut witness_next_ldes_on_coset = vec![];

        for (idx, w) in assignment_polynomials.clone().into_iter().enumerate() {
            let monomial = w.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
            witness_polys_in_monomial_form.push(monomial.clone());

            // this is D polynomial and we need to make next
            if idx == <PlonkCsWidth4WithNextStepParams as PlonkConstraintSystemParams<E>>::STATE_WIDTH - 1 {
                let mut d_next = monomial.clone();
                d_next.distribute_powers(&worker, d_next.omega);

                let lde = d_next.bitreversed_lde_using_bitreversed_ntt(
                    &worker, 
                    LDE_FACTOR, 
                    omegas_bitreversed, 
                    &coset_factor
                )?;

                witness_next_ldes_on_coset.push(lde);
            }

            let lde = monomial.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                LDE_FACTOR, 
                omegas_bitreversed, 
                &coset_factor
            )?;
            witness_ldes_on_coset.push(lde);
        }


        // PLOOKUP         
        
        let new_domain_size = required_domain_size*8;

        let lookup_selector_poly_index = setup.selector_polynomials.len() -1;
        let lookup_selector_poly = setup.selector_polynomials[lookup_selector_poly_index].clone();
        let lookup_selector = lookup_selector_poly.clone().fft(worker);        

        // use this challenge until there will be enough entropy to put in transcript
        let plookup_challenge = E::Fr::from_str("42").unwrap();
        let mut plookup_challenge_square = plookup_challenge.clone();
        plookup_challenge_square.mul_assign(&plookup_challenge);

        let mut beta_one = beta.clone();
        beta_one.add_assign(&E::Fr::one());

        let mut gamma_beta_one = beta_one.clone();
        gamma_beta_one.mul_assign(&gamma);

        let gamma_beta_one_poly = Polynomial::from_values(vec![gamma_beta_one; new_domain_size])?;

        let (s_poly, shifted_s_poly, s_original) = {
            let count = required_domain_size - num_lookup_gates - lookup_table.len();
            // construct s = (f,t) sorted by t               
            let mut s_vec = vec![MultiSet::<E>::new();count];
            for i in 0..full_assignments[0].len(){
                if lookup_selector.as_ref()[i] == E::Fr::one(){
                    s_vec.push(MultiSet::from_vec([full_assignments[0][i], full_assignments[1][i], full_assignments[2][i]]));
                }
            }

            for i in 0..lookup_table.len(){
                s_vec.push(MultiSet::from_vec([lookup_table[i].0, lookup_table[i].1, lookup_table[i].2]));
            }

            // sort s based on multiset
            s_vec.sort();


            let s: Vec<E::Fr >= s_vec.iter().map(|m| m.scale_and_sum(plookup_challenge)).collect();

            let s = Polynomial::from_values(s)?;
            let s_original = s.clone();
            let factor = ((new_domain_size / s.size()) as usize).next_power_of_two();
            let s = s.ifft(worker);                
            let omega = s.omega.clone();
            let mut shifted_s  = s.clone();
            shifted_s.distribute_powers(&worker, omega);
            let s = s.lde(worker,factor)?;
            let shifted_s = shifted_s.lde(worker, factor)?;             
            
            (s, shifted_s, s_original)
        };

        let (witness_poly, witness_original, lookup_original) = {
            // f(x) = (a(x) + b(x)*plookup_challenge + c(x)*plookup_challenge^2) * q_lookup(x)
            let mut witness_poly = assignment_polynomials[0].clone();
            let mut bx = assignment_polynomials[1].clone();
            bx.scale(&worker, plookup_challenge);
            witness_poly.add_assign(&worker, &bx);
            let mut cx= assignment_polynomials[2].clone();
            cx.scale(&worker, plookup_challenge_square);
            witness_poly.add_assign(&worker, &cx);

            let witness_poly = witness_poly.clone_padded_to_domain()?;
            let witness_original = witness_poly.clone();

            let factor = ((new_domain_size / witness_poly.size()) as usize).next_power_of_two();           
            let mut witness_poly = witness_poly.ifft(worker).lde(worker, factor)?;            

            let lookup_original = lookup_selector_poly.clone().fft(&worker);

            let lookup_poly = lookup_selector_poly.lde(worker, factor)?;
            witness_poly.mul_assign(&worker, &lookup_poly);
            
            
            (witness_poly,witness_original, lookup_original)

        };

        let (table_poly, shifted_table_poly, table_original) = {
            // t(x) = t_1(x) + t_2(x)*plookup_challenge + t_3(x)* plookup_challenge^2 
            let mut t1_values = vec![E::Fr::zero(); required_domain_size-lookup_table.len()];
            let mut t2_values = vec![E::Fr::zero(); required_domain_size-lookup_table.len()];
            let mut t3_values = vec![E::Fr::zero(); required_domain_size-lookup_table.len()];
            for i in 0..lookup_table.len(){
                t1_values.push(lookup_table[i].0);
                t2_values.push(lookup_table[i].1);
                t3_values.push(lookup_table[i].2);
            }

            let t1 = Polynomial::from_values(t1_values)?;
            let mut t2 = Polynomial::from_values(t2_values)?;
            let mut t3 = Polynomial::from_values(t3_values)?;

            let mut table_poly = t1.clone();
            t2.scale(&worker, plookup_challenge);
            table_poly.add_assign(&worker, &t2);
            t3.scale(&worker, plookup_challenge_square);
            table_poly.add_assign(&worker, &t3);

            let table_original = table_poly.clone();
            let factor = ((new_domain_size / table_poly.size()) as usize).next_power_of_two();
            let omega = table_poly.omega.clone();
            let table_poly = table_poly.ifft(worker);
            let mut shifted_table_poly = table_poly.clone();
            shifted_table_poly.distribute_powers(&worker, omega);

            let table_poly = table_poly.lde(worker, factor)?;
            let shifted_table_poly = shifted_table_poly.lde(&worker, factor)?;
            
            (table_poly,shifted_table_poly, table_original)
        };        

        let (plookup_z, plookup_shifted_z) = {
            let number_of_steps = witness_original.as_ref().len()-1;

            let mut z_evals = vec![E::Fr::one(); number_of_steps+1];

            let mut new_witness_original = vec![E::Fr::zero(); number_of_steps+1];

            for (i, (original, new)) in witness_original.as_ref().iter().zip(new_witness_original.iter_mut()).enumerate(){
                if lookup_original.as_ref()[i] == E::Fr::one(){
                    *new = *original;
                }
            }

            for i in 0..number_of_steps{
                let mut witness_part = gamma.clone();
                witness_part.add_assign(&new_witness_original[i]);

                let mut table_part = table_original.as_ref()[i+1];
                table_part.mul_assign(&beta);                
                table_part.add_assign(&table_original.as_ref()[i]);
                table_part.add_assign(&gamma_beta_one);

                let mut s_part = s_original.as_ref()[i+1].clone();
                s_part.mul_assign(&beta);
                s_part.add_assign(&s_original.as_ref()[i]);
                s_part.add_assign(&gamma_beta_one);

                let den = s_part.inverse().expect("should have inverse"); // TODO: batch inverse

                let mut num = beta_one.clone();
                num.mul_assign(&witness_part);
                num.mul_assign(&table_part);

                num.mul_assign(&den);
                
                let prev = z_evals[i].clone();

                z_evals[i+1].mul_assign(&prev);
                z_evals[i+1].mul_assign(&num);
            }

            let z = Polynomial::from_values(z_evals)?;

            let mut shifted_z_monomial = z.clone().ifft(&worker);
            let omega = z.omega.clone();
            shifted_z_monomial.distribute_powers(&worker, omega);
            let shifted_z = shifted_z_monomial.fft(&worker);

            let expected = gamma_beta_one.pow([(number_of_steps) as u64]);
            assert_eq!(shifted_z.as_ref()[number_of_steps-1], expected);
            assert_eq!(z.as_ref()[0], E::Fr::one());

            for (i, (sz, z)) in shifted_z.as_ref().iter().zip(z.as_ref().iter()).enumerate(){
                // println!(" {} {} {}", z, sz, gamma_beta_one.pow([(number_of_steps-i) as u64]));
            }

            
            (z, shifted_z)
        };

            
        // TODO:  Z(x*omega) * (\gamma (1 + \beta) + s(x) + \beta * s(x*omega) - Z(x)* (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega) = 0
        
        let  plookup_num = {        
            let gamma_poly = Polynomial::from_values(vec![gamma; new_domain_size])?;
            let beta_one_poly = Polynomial::from_values(vec![beta_one; new_domain_size])?;

            let mut num = witness_poly.clone();
            num.add_assign(&worker, &gamma_poly);    
            let mut shifted_table_poly = shifted_table_poly.clone();
            shifted_table_poly.scale(&worker, beta);
            shifted_table_poly.add_assign(&worker, &table_poly);
            shifted_table_poly.add_assign(&worker, &gamma_beta_one_poly);
            num.mul_assign(&worker, &shifted_table_poly);

            num.mul_assign(&worker, &beta_one_poly);
            
            num
        };

        let plookup_den = {
            let mut den = shifted_s_poly.clone();
            den.scale(&worker, beta);
            den.add_assign(&worker, &s_poly);
            den.add_assign(&worker, &gamma_beta_one_poly);
            // den.batch_inversion(&worker)?;

            den
        };
    

        let domain_size_for_quotient = new_domain_size;

        let mut plookup_polynomials = vec![plookup_shifted_z, plookup_den, plookup_z, plookup_num];

        for p in plookup_polynomials.iter_mut(){
            let factor = ((domain_size_for_quotient / p.size()) as usize).next_power_of_two();
            *p = p.clone().ifft(&worker).lde(&worker, factor)?;
        }
    
        // plookup_polynomials[0].as_ref().iter().for_each(|e| println!("{}", e));

        let mut plookup_t = plookup_polynomials[0].clone();
        plookup_t.mul_assign(&worker, &plookup_polynomials[1]);

        let mut tmp = plookup_polynomials[2].clone();
        tmp.mul_assign(&worker, &plookup_polynomials[3]);

        plookup_t.sub_assign(&worker, &tmp);

        let mut vanishing_poly_of_plookup =
        evaluate_vanishing_polynomial_of_degree_on_domain_size::<E::Fr>(
            required_domain_size as u64,
            &E::Fr::multiplicative_generator(),
            domain_size_for_quotient as u64,
            &worker,
        )?;
        vanishing_poly_of_plookup.batch_inversion(&worker)?;

        plookup_t.mul_assign(&worker, &vanishing_poly_of_plookup);

        let plookup_t_poly = plookup_t.icoset_fft_for_generator(&worker, &E::Fr::multiplicative_generator());

        plookup_t_poly.as_ref().iter().enumerate().for_each(|(i, e)| println!("{} {}", i, e));


        let alpha = transcript.get_challenge();

        // calculate first part of the quotient polynomial - the gate itself
        // A + B + C + D + AB + CONST + D_NEXT == 0 everywhere but on the last point of the domain
        
        // after introducing new lookup selector, constant selector is shifted one step to the left
        let selector_q_const_index = setup.selector_polynomials.len()-2;
        
        let mut quotient_linearization_challenge = E::Fr::one();

        let (mut t_1, mut tmp) = {
            // Include the public inputs
            let mut inputs_poly = Polynomial::<E::Fr, Values>::new_for_size(required_domain_size)?;
            for (idx, &input) in input_values.iter().enumerate() {
                inputs_poly.as_mut()[idx] = input;
            }
            // go into monomial form

            let mut inputs_poly = inputs_poly.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

            // add constants selectors vector            
            inputs_poly.add_assign(&worker, &setup.selector_polynomials[selector_q_const_index]);

            // LDE
            let mut t_1 = inputs_poly.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                LDE_FACTOR, 
                omegas_bitreversed, 
                &coset_factor
            )?;

            // Q_A * A
            let mut tmp = setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[0].clone();
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            t_1.add_assign(&worker, &tmp);

            // Q_B * B
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[1]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            // Q_C * C
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[2]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[2]);
            t_1.add_assign(&worker, &tmp);

            // Q_D * D
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[3]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[3]);
            t_1.add_assign(&worker, &tmp);

            // Q_M * A * B
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[4]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            tmp.reuse_allocation(&setup_precomputations.next_step_selector_polynomials_on_coset_of_size_4n_bitreversed[0]);
            tmp.mul_assign(&worker, &witness_next_ldes_on_coset[0]);
            t_1.add_assign(&worker, &tmp);

            (t_1, tmp)
        };

        // drop(witness_ldes_on_coset);
        drop(witness_next_ldes_on_coset);

        // now compute the permutation argument

        let z_coset_lde_bitreversed = z_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            LDE_FACTOR, 
            omegas_bitreversed, 
            &coset_factor
        )?;

        assert!(z_coset_lde_bitreversed.size() == required_domain_size*LDE_FACTOR);

        let z_shifted_coset_lde_bitreversed = z_shifted_in_monomial_form.bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            LDE_FACTOR, 
            omegas_bitreversed, 
            &coset_factor
        )?;

        assert!(z_shifted_coset_lde_bitreversed.size() == required_domain_size*LDE_FACTOR);

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
            tmp.add_assign_scaled(&worker, &setup_precomputations.x_on_coset_of_size_4n_bitreversed, &beta);
            contrib_z.mul_assign(&worker, &tmp);

            assert_eq!(non_residues.len() + 1, witness_ldes_on_coset.len());

            for (w, non_res) in witness_ldes_on_coset[1..].iter().zip(non_residues.iter()) {
                let mut factor = beta;
                factor.mul_assign(&non_res);

                tmp.reuse_allocation(&w);
                tmp.add_constant(&worker, &gamma);
                tmp.add_assign_scaled(&worker, &setup_precomputations.x_on_coset_of_size_4n_bitreversed, &factor);
                contrib_z.mul_assign(&worker, &tmp);
            }

            t_1.add_assign_scaled(&worker, &contrib_z, &quotient_linearization_challenge);

            drop(contrib_z);

            let mut contrib_z = z_shifted_coset_lde_bitreversed;

            // A + beta*perm_a + gamma

            assert_eq!(
                setup_precomputations.permutation_polynomials_on_coset_of_size_4n_bitreversed.len(), witness_ldes_on_coset.len()
            );

            for (w, perm) in witness_ldes_on_coset.iter()
            .zip(setup_precomputations.permutation_polynomials_on_coset_of_size_4n_bitreversed.iter()) {
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

        let l_0 = calculate_lagrange_poly::<E::Fr>(&worker, required_domain_size.next_power_of_two(), 0)?;

        {
            let mut z_minus_one_by_l_0 = z_coset_lde_bitreversed;
            z_minus_one_by_l_0.sub_constant(&worker, &E::Fr::one());

            let l_coset_lde_bitreversed = l_0.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                LDE_FACTOR, 
                omegas_bitreversed, 
                &coset_factor
            )?;

            z_minus_one_by_l_0.mul_assign(&worker, &l_coset_lde_bitreversed);

            t_1.add_assign_scaled(&worker, &z_minus_one_by_l_0, &quotient_linearization_challenge);

            drop(z_minus_one_by_l_0);
        }

        drop(tmp);

        t_1.mul_assign(&worker, &setup_precomputations.inverse_divisor_on_coset_of_size_4n_bitreversed);

        t_1.bitreverse_enumeration(&worker);

        let t_poly_in_monomial_form = t_1.icoset_fft_for_generator(&worker, &E::Fr::multiplicative_generator());

        let mut t_poly_parts = t_poly_in_monomial_form.break_into_multiples(required_domain_size)?;

        for t_part in t_poly_parts.iter() {
            let t_part_commitment = commit_using_monomials(
                &t_part, 
                &crs_mon, 
                &worker
            )?;

            commit_point_as_xy::<E, _>(&mut transcript, &t_part_commitment);

            proof.quotient_poly_commitments.push(t_part_commitment);
        }

        // draw random point

        let z = transcript.get_challenge();
        let mut z_by_omega = z;
        z_by_omega.mul_assign(&domain.generator);

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

        proof.quotient_polynomial_at_z = t_at_z;

        for el in proof.wire_values_at_z.iter() {
            transcript.commit_field_element(el);
        }

        for el in proof.wire_values_at_z_omega.iter() {
            transcript.commit_field_element(el);
        }

        for el in proof.permutation_polynomials_at_z.iter() {
            transcript.commit_field_element(el);
        }

        transcript.commit_field_element(&proof.quotient_polynomial_at_z);

        // now compute linearization_polynomial in a monomial form

        let mut quotient_linearization_challenge = E::Fr::one();

        let r = {
            // Q_const
            let mut r = setup.selector_polynomials[selector_q_const_index].clone();

            // Q_A * A(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[0], &proof.wire_values_at_z[0]);

            // Q_B * B(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[1], &proof.wire_values_at_z[1]);

            // Q_C * C(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[2], &proof.wire_values_at_z[2]);

            // Q_D * D(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[3], &proof.wire_values_at_z[3]);

            // Q_M * A(z) * B(z)
            let mut scaling_factor = proof.wire_values_at_z[0];
            scaling_factor.mul_assign(&proof.wire_values_at_z[1]);
            r.add_assign_scaled(&worker, &setup.selector_polynomials[4], &scaling_factor);

            // Q_D_Next * D(z*omega)

            r.add_assign_scaled(&worker, &setup.next_step_selector_polynomials[0], &proof.wire_values_at_z_omega[0]);

            quotient_linearization_challenge.mul_assign(&alpha);

            // + (a(z) + beta*z + gamma)*()*()*()*Z(x)

            let mut factor = quotient_linearization_challenge;
            for (wire_at_z, non_residue) in proof.wire_values_at_z.iter()
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

            for (wire_at_z, perm_at_z) in proof.wire_values_at_z.iter()
                            .zip(proof.permutation_polynomials_at_z.iter())
            {
                let mut t = *perm_at_z;
                t.mul_assign(&beta);
                t.add_assign(&wire_at_z);
                t.add_assign(&gamma);

                factor.mul_assign(&t);
            }

            r.sub_assign_scaled(&worker, &setup.permutation_polynomials.last().expect("last permutation poly"), &factor);

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
            let mut lhs = t_at_z;
            let vanishing_at_z = evaluate_vanishing_for_size(&z ,required_domain_size as u64);
            lhs.mul_assign(&vanishing_at_z);

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

            assert_eq!(proof.permutation_polynomials_at_z.len() + 1, proof.wire_values_at_z.len());

            for (w, p) in proof.wire_values_at_z.iter().zip(proof.permutation_polynomials_at_z.iter()) {
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

            if lhs != rhs {
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

        multiopening_challenge.mul_assign(&v);

        let mut poly_to_divide_at_z_omega = z_in_monomial_form;
        poly_to_divide_at_z_omega.scale(&worker, multiopening_challenge);

        multiopening_challenge.mul_assign(&v);

        // d should be opened at z*omega due to d_next
        poly_to_divide_at_z_omega.add_assign_scaled(&worker, &witness_polys_in_monomial_form[3], &multiopening_challenge);
        drop(witness_polys_in_monomial_form);

        debug_assert_eq!(multiopening_challenge, v.pow(&[(1 + 4 + 3 + 1 + 1) as u64]));

        // division in monomial form is sequential, so we parallelize the divisions

        let mut polys = vec![(poly_to_divide_at_z, z), (poly_to_divide_at_z_omega, z_by_omega)];

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

        let opening_at_z = commit_using_monomials(
            &open_at_z, 
            &crs_mon,
            &worker
        )?;

        let opening_at_z_omega = commit_using_monomials(
            &open_at_z_omega, 
            &crs_mon,
            &worker
        )?;

        proof.opening_at_z_proof = opening_at_z;
        proof.opening_at_z_omega_proof = opening_at_z_omega;
        
        Ok(proof)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::verifier::verify;

    use crate::pairing::Engine;

    #[derive(Clone)]
    struct TestCircuit4<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E, PlonkCsWidth4WithNextStepParams> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E, PlonkCsWidth4WithNextStepParams> >(&self, cs: &mut CS) -> Result<(), SynthesisError> {        
            let  zero = E::Fr::zero();
            let  one = E::Fr::one();
            let mut neg_one = E::Fr::one();
            neg_one.negate();

            let count = 2;
            for i in 0..count{
                for j in 0..count{
                    let left_val = E::Fr::from_str(&j.to_string()).unwrap();
                    let right_val = E::Fr::from_str(&i.to_string()).unwrap();

                    let left = cs.alloc(||{
                        Ok(left_val)
                    })?;
                    
                    let right = cs.alloc(||{
                        Ok(right_val)
                    })?;

                 
                    // lookup gate
                    let result = cs.read_from_table(left, right)?;
                    let result_val = cs.get_value(result)?;
                    let add = cs.alloc(||{
                        let mut sum = left_val.clone();
                        sum.add_assign(&right_val);
                        sum.add_assign(&result_val);
                        Ok(sum)
                    })?;

                    cs.new_gate(
                        [left, right, result, add], 
                        [one, one, one, neg_one, zero, zero, zero],
                        [zero]
                    )?;

                }
            }

            Ok(())
        }
    }

    #[test]
    fn test_plookup_prover() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;
        use crate::plonk::plookup::generator::*;
        use crate::plonk::plookup::keys::*;

        let size = 256;
        let bit_size = 2;
        let mut table = vec![];
        for i in 0..bit_size{
            for j in 0..bit_size{
                let k = i ^ j;
                let a = Fr::from_str(&j.to_string()).unwrap();
                let b = Fr::from_str(&i.to_string()).unwrap();
                let c = Fr::from_str(&k.to_string()).unwrap();
                table.push((a,b,c));
            }
        }

        let mut assembly = GeneratorAssembly4WithNextStep::<Bn256>::new_with_lookup_table(table.clone());

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.clone().synthesize(&mut assembly).expect("must work");

        // println!("{:?}", assembly);

        assembly.finalize();

        let worker = Worker::new();

        let setup = assembly.setup(&worker).unwrap();

        let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals = Crs::<Bn256, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        let verification_key = VerificationKey::from_setup(
            &setup, 
            &worker, 
            &crs_mons
        ).unwrap();

        // println!("Verification key = {:?}", verification_key);

        let precomputations = SetupPolynomialsPrecomputations::from_setup(
            &setup, 
            &worker
        ).unwrap();

       

        let mut assembly = ProverAssembly4WithNextStep::<Bn256>::new_with_lookup_table(table);

        circuit.clone().synthesize(&mut assembly).expect("must work");

        assembly.finalize();
    
        let size = setup.permutation_polynomials[0].size();

        type Transcr = Blake2sTranscript<Fr>;

        let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size(size.next_power_of_two());

        let proof = assembly.prove::<Transcr, _, _>(
            &worker,
            &setup,
            &precomputations,
            &crs_vals,
            &crs_mons,
            &omegas_bitreversed,
            &omegas_inv_bitreversed,
        ).unwrap();

        let is_valid = verify::<Bn256, PlonkCsWidth4WithNextStepParams, Transcr>(&proof, &verification_key).unwrap();

        assert!(is_valid);

        assert!(Fr::zero() < Fr::one());

    }

    #[test]
    fn test_multiset_sort(){
        use crate::pairing::bn256::{Bn256, Fr};
        use super::MultiSet;
        let one = Fr::one();
        let mut two = one.clone();
        two.double();
        let mut three = two.clone();
        three.add_assign(&one);

        let m0 = MultiSet::<Bn256>([three, two, three]);
        let m1 = MultiSet::<Bn256>([three, two, three]);
        let m2 = MultiSet::<Bn256>([three, two, one]);
        let m3 = MultiSet::<Bn256>([two, two, three]);

        assert_ne!(m1, m2);
        assert_eq!(m0, m1);

        assert!(m1 > m2);
        assert!(m2 < m3);
        assert!(m1 > m3);
    }  
    
    #[test]
    fn test_plonk_shifted_poly(){
        use crate::plonk::polynomials::{Polynomial, Values};
        use crate::multicore::Worker;
        use crate::pairing::bls12_381::{Bls12, Fr};

        let one = Fr::from_str("1").unwrap();
        let two = Fr::from_str("2").unwrap();
        let three = Fr::from_str("3").unwrap();
        let four = Fr::from_str("4").unwrap();

        let worker = Worker::new();

        let p = Polynomial::from_values(vec![one, two, three, four]).unwrap();

        let p_poly = p.clone().ifft(&worker);

        let mut generator = p.omegainv.clone();
        generator.mul_assign(&p.omegainv);
        let mut shifted = p.clone().ifft(&worker);
        shifted.distribute_powers(&worker, generator);
        let shifted = shifted.fft(&worker);
        shifted.as_ref().iter().for_each(|e| println!("{}", e));
    
    }

    #[test]
    fn test_plookup_manually(){
        use crate::plonk::polynomials::{Polynomial, Values};
        use crate::multicore::Worker;
        use crate::pairing::bls12_381::{Bls12, Fr};

        let zero = Fr::zero();
        let one = Fr::one();
        let two = Fr::from_str("2").unwrap();
        let three = Fr::from_str("3").unwrap();

        // lookup gate selectors
        let gs0 = Fr::one();
        let gs1 = Fr::one();
        let gs2 = Fr::one();

        let lookup_selectors = vec![gs0, gs1, gs2];

        // lookup gate assignments
        let g0 = MultiSet::<Bls12>::from_vec([one, two, three]);        // 1 ^ 2 = 3
        let g1 = MultiSet::<Bls12>::from_vec([one, three, two]);        // 1 ^ 3 = 2
        let g2 = MultiSet::<Bls12>::from_vec([two, three, one]);        // 2 ^ 3 = 1
        // let g3 = MultiSet::<Bls12>::from_vec([three, one, two]);        // 3 ^ 1 = 2

        let lookup_gates = vec![g0, g1, g2];

        // table elements
        // let t00 = MultiSet::<Bls12>::from_vec([zero, zero, zero]);      // 0 ^ 0 = 0
        // let t10 = MultiSet::<Bls12>::from_vec([one, zero, one]);        // 1 ^ 0 = 1
        // let t20 = MultiSet::<Bls12>::from_vec([two, zero, two]);        // 2 ^ 0 = 2
        // let t30 = MultiSet::<Bls12>::from_vec([three, zero, three]);    // 3 ^ 0 = 3

        let t01 = MultiSet::<Bls12>::from_vec([zero, one, one]);        // 0 ^ 1 = 1
        let t11 = MultiSet::<Bls12>::from_vec([one, one, zero]);        // 1 ^ 1 = 0
        let t21 = MultiSet::<Bls12>::from_vec([two, one, three]);       // 2 ^ 1 = 3
        let t31 = MultiSet::<Bls12>::from_vec([three, one, two]);       // 3 ^ 1 = 2

        let t02 = MultiSet::<Bls12>::from_vec([zero, two, two]);        // 0 ^ 2 = 2
        let t12 = MultiSet::<Bls12>::from_vec([one, two, three]);       // 1 ^ 2 = 3
        let t22 = MultiSet::<Bls12>::from_vec([two, two, zero]);        // 2 ^ 2 = 0
        let t32 = MultiSet::<Bls12>::from_vec([three, two, one]);       // 3 ^ 2 = 1

        let t03 = MultiSet::<Bls12>::from_vec([zero, three, three]);    // 0 ^ 3 = 3
        let t13 = MultiSet::<Bls12>::from_vec([one, three, two]);       // 1 ^ 3 = 2
        let t23 = MultiSet::<Bls12>::from_vec([two, three, one]);       // 2 ^ 3 = 1
        let t33 = MultiSet::<Bls12>::from_vec([three, three, zero]);    // 3 ^ 3 = 0

        let  table_rows = vec![t01, t11, t21,t31, t02,t12,t22,t32, t03, t13,t23,t33];

        let n = lookup_gates.len() + table_rows.len();
        assert_eq!(n, 15);

        // challenges
        let beta = Fr::from_str("37").unwrap();
        let gamma = Fr::from_str("43").unwrap();
        let kappa = Fr::from_str("42").unwrap();

        // construct s
        let mut s_agg = vec![Fr::zero()];
        lookup_gates.iter().chain(table_rows.iter()).for_each(|m| s_agg.push(m.scale_and_sum(kappa)));
        assert_eq!(s_agg.len(), n);
        
        // sort s
        s_agg.sort();
        
        
        let domain_size = (n+1).next_power_of_two();

        // prepend zeroes
        let mut lookup_selectors_resized = lookup_selectors.clone();
        lookup_selectors_resized.resize(domain_size - lookup_selectors.len(), Fr::zero());

        let mut lookup_gates_resized = lookup_gates.clone();
        lookup_gates_resized.resize(domain_size - lookup_gates.len(), MultiSet::new());
        
        // append zeroes
        let mut table_rows_resized = vec![MultiSet::new(); domain_size-table_rows.len()];
        table_rows.iter().for_each(|m| table_rows_resized.push(m.clone()));

        // scale and sum lookup gates
        let lookup_gate_values: Vec<Fr> = lookup_gates.iter().map(|m| m.scale_and_sum(kappa)).collect();
        
        // scale and sum table rows
        let table_row_values: Vec<Fr> = table_rows.iter().map(|m| m.scale_and_sum(kappa)).collect();
        
        // scale and sum s aggregation
        let s_values = s_agg.clone();


                
        let mut beta_one = beta.clone();
        beta_one.add_assign(&Fr::one());
        let mut gamma_beta_one = beta_one.clone();
        gamma_beta_one.mul_assign(&gamma);



        let z0_num = Fr::one();
        let z1_den = Fr::one();
        let z0 = Fr::one();

        
        fn eval(before: Fr, witness: Fr, t: Fr, t_shifted: Fr, s: Fr, s_shifted: Fr) -> Fr{

            Fr::one()
        }
        
        // z1 = z0 * (1+beta) * F0(beta,gamma) / G0(beta, gamma)
        let z1 = eval(z0, lookup_gate_values[0], table_row_values[0], table_row_values[1], s_values[0], s_values[1]);
        // z2 = z1 * (1+beta) * F1(beta,gamma) / G1(beta, gamma)
        let z2 = eval(z0, lookup_gate_values[1], table_row_values[1], table_row_values[2], s_values[1], s_values[2]);
        // z3 = z2 * (1+beta) * F2(beta,gamma) / G2(beta, gamma)
        let z3 = eval(z0, lookup_gate_values[2], table_row_values[2], table_row_values[3], s_values[2], s_values[3]);
    }
}