use crate::pairing::ff::PrimeField;
use super::lookup_table::TableType;

use std::cmp::Ordering;

#[derive(Debug, Clone)]
pub struct MultiSet<F: PrimeField>([F; 4]);

impl<F: PrimeField> MultiSet<F>{
    pub fn new()-> Self{
        Self([F::zero();4])
    }
    pub fn from_vec(vec: [F;4])-> Self{
        Self(vec)
    }

    pub fn scale_and_sum(&self , s: F, is_range_lookup: bool) -> F{
        let mut scalar = F::one();
        let mut sum = F::zero();

        let mut values = vec![];

        if is_range_lookup{
            values.push(self.0[0])
        }else{
            values.extend_from_slice(&self.0)
        }

        values.iter().for_each(|e| {
            let mut tmp = e.clone();
            tmp.mul_assign(&scalar);
            sum.add_assign(&tmp);
            scalar.mul_assign(&s);
        }); 

        sum
    }
}

impl<F: PrimeField> PartialEq for MultiSet<F>{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0[0] == other.0[0] && self.0[1] == other.0[1] && self.0[2] == other.0[2] &&  self.0[3] == other.0[3]
    }
}

impl<F: PrimeField> Eq for MultiSet<F>{}

impl<F: PrimeField> PartialOrd for MultiSet<F>{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {       
        Some(self.cmp(other))
    }
}

impl<F: PrimeField> Ord for MultiSet<F>{
    fn cmp(&self, other: &Self) -> Ordering {
        // TODO: better handle
        // table index is not involved comparison
        let s0 = self.0[0].into_repr();
        let s1 = self.0[1].into_repr();
        
        let o0 = other.0[0].into_repr();
        let o1 = other.0[1].into_repr();

        if s1 < o1{
            Ordering::Less
        }else if s1 > o1{
            Ordering::Greater
        }else{
            if s0 < o0{
                Ordering::Less
            }else{
                Ordering::Greater
            }
        }
    }
}


#[test]
fn test_multiset_sort(){
    use crate::pairing::bn256::{Bn256, Fr};
    use crate::pairing::ff::Field;
    let one = Fr::one();
    let two = Fr::from_str("2").unwrap();
    let three = Fr::from_str("3").unwrap();
    let four = Fr::from_str("4").unwrap();

    let m0 = MultiSet::<Fr>([three, two, three, four]);
    let m1 = MultiSet::<Fr>([three, two, three, four]);
    let m2 = MultiSet::<Fr>([three, two, one, four]);
    let m3 = MultiSet::<Fr>([two, two, three, four]);

    assert_ne!(m1, m2);
    assert_eq!(m0, m1);

    assert!(m1 > m2);
    assert!(m2 < m3);
    assert!(m1 > m3);
}