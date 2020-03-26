use crate::pairing::Engine;
use crate::pairing::ff::{Field, PrimeField};

#[derive(Copy,Clone)]
pub struct Oracles<E: Engine>{
    pub alpha: E::Fr,
    pub eta_a: E::Fr,
    pub eta_b: E::Fr,
    pub eta_c: E::Fr,
    pub beta_one: E::Fr,
    pub beta_two: E::Fr,
    pub beta_three: E::Fr,
}

impl<E: Engine> Oracles<E>{
    pub fn new() -> Self{
        Oracles{
            alpha: E::Fr::zero(),
            eta_a: E::Fr::zero(),            
            eta_b: E::Fr::zero(),            
            eta_c: E::Fr::zero(),            
            beta_one: E::Fr::zero(),            
            beta_two: E::Fr::zero(),            
            beta_three: E::Fr::zero(),            
        }
    }
}