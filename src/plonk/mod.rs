pub mod adaptor;
pub mod cs;
// pub mod generator;
// pub mod prover;
// pub mod verifier;
// pub mod tester;
pub mod polynomials;
pub mod domains;
pub mod fft;
pub mod utils;
pub mod transparent_engine;

pub mod redshift;

pub mod plonk;
pub mod plookup;

pub mod commitments;

pub mod better_cs;

pub use self::better_cs::adaptor::{TranspilationVariant, Transpiler, Adaptor, AdaptorCircuit};
pub use self::better_cs::keys::{SetupPolynomials, SetupPolynomialsPrecomputations, VerificationKey, Proof};

use crate::pairing::Engine;
use crate::{SynthesisError, Circuit};
use crate::multicore::Worker;
use crate::kate_commitment::*;
use self::better_cs::cs::{PlonkCsWidth4WithNextStepParams, PlonkConstraintSystemParams};
use crate::plonk::commitments::transcript::*;
use crate::plonk::fft::cooley_tukey_ntt::*;

pub fn transpile<E: Engine, C: crate::Circuit<E>>(circuit: C) -> Result<Vec<(usize, TranspilationVariant)>, SynthesisError> {
    let mut transpiler = Transpiler::<E, PlonkCsWidth4WithNextStepParams>::new();

    circuit.synthesize(&mut transpiler).expect("sythesize into traspilation must succeed");

    let hints = transpiler.into_hints();

    Ok(hints)
}

pub fn is_satisfied<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<(), SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::test_assembly::TestAssembly::new();

    adapted_curcuit.synthesize(&mut assembly)
}

pub fn is_satisfied_using_one_shot_check<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<(), SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::one_shot_test_assembly::OneShotTestAssembly::new();

    adapted_curcuit.synthesize(&mut assembly)?;

    let valid = assembly.is_satisfied(false);

    if valid {
        return Ok(());
    } else {
        return Err(SynthesisError::Unsatisfiable);
    }
}

pub fn setup<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::generator::GeneratorAssembly::<E, PlonkCsWidth4WithNextStepParams>::new();

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let worker = Worker::new();

    assembly.setup(&worker)
}

pub fn make_verification_key<E: Engine, P: PlonkConstraintSystemParams<E>>(
    setup: &SetupPolynomials<E, P>,
    crs: &Crs<E, CrsForMonomialForm>
) -> Result<VerificationKey<E, P>, SynthesisError> {
    let worker = Worker::new();

    let verification_key = VerificationKey::from_setup(
        &setup, 
        &worker, 
        &crs
    )?;

    Ok(verification_key)
}

pub fn make_precomputations<E: Engine, P: PlonkConstraintSystemParams<E>>(
    setup: &SetupPolynomials<E, P>
) -> Result<SetupPolynomialsPrecomputations<E, P>, SynthesisError> {
    let worker = Worker::new();

    let precomputations = SetupPolynomialsPrecomputations::from_setup(
        &setup, 
        &worker, 
    )?;

    Ok(precomputations)
}

pub fn prove<E: Engine, C: crate::Circuit<E>, T: Transcript<E::Fr>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>,
    setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
    csr_mon_basis: &Crs<E, CrsForMonomialForm>,
    crs_lagrange_basis: &Crs<E, CrsForLagrangeForm>
) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let precomputations = make_precomputations(&setup)?;

    // TODO: keep track of num AUX too
    let mut assembly = self::better_cs::prover::ProverAssembly::new_with_size_hints(setup.num_inputs, setup.n);

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let size = setup.n.next_power_of_two();

    let worker = Worker::new();

    let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
    let omegas_inv_bitreversed = <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(size.next_power_of_two());

    use std::time::Instant;
    let now = Instant::now();
    let proof = assembly.prove::<T, _, _>(
        &worker,
        &setup,
        &precomputations,
        &crs_lagrange_basis,
        &csr_mon_basis,
        &omegas_bitreversed,
        &omegas_inv_bitreversed,
    )?;

    println!("Proving taken {:?}", now.elapsed());

    Ok(proof)
}


pub fn prove_from_recomputations<
    E: Engine, 
    C: crate::Circuit<E>, 
    T: Transcript<E::Fr>,
    CP: CTPrecomputations<E::Fr>,
    CPI: CTPrecomputations<E::Fr>,
>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>,
    setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
    setup_precomputations: &SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>,
    omegas_bitreversed: &CP,
    omegas_inv_bitreversed: &CPI,
    csr_mon_basis: &Crs<E, CrsForMonomialForm>,
    crs_lagrange_basis: &Crs<E, CrsForLagrangeForm>
) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::prover::ProverAssembly::new_with_size_hints(setup.num_inputs, setup.n);

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let size = setup.n.next_power_of_two();

    assert_eq!(omegas_bitreversed.domain_size(), size);
    assert_eq!(omegas_inv_bitreversed.domain_size(), size);

    let worker = Worker::new();

    use std::time::Instant;
    let now = Instant::now();
    let proof = assembly.prove::<T, _, _>(
        &worker,
        &setup,
        &setup_precomputations,
        &crs_lagrange_basis,
        &csr_mon_basis,
        omegas_bitreversed,
        omegas_inv_bitreversed,
    )?;

    println!("Proving taken {:?}", now.elapsed());

    Ok(proof)
}

pub fn verify<E: Engine, T: Transcript<E::Fr>>(
    proof: &Proof<E, PlonkCsWidth4WithNextStepParams>,
    verification_key: &VerificationKey<E, PlonkCsWidth4WithNextStepParams>
) -> Result<bool, SynthesisError> {
    self::better_cs::verifier::verify::<E, PlonkCsWidth4WithNextStepParams, T>(&proof, &verification_key)
}