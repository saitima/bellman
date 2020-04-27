use crate::pairing::ff::PrimeField;
use std::fmt;

#[derive(Clone)]
pub enum TableType{
    XOR = 1,
    AND = 2,
}

impl fmt::Display for TableType{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { 
        let type_as_int = match self{
            Self::XOR => 1,
            Self::AND => 2,
        };
        write!(f, "{}", type_as_int)
     }
}



pub trait LookupTable<F: PrimeField>{
    fn lookup_type(&self) -> TableType;
    fn lookup_type_as_fe(&self) -> F;
    fn query(&self, _: F, _: F) -> Option<F>;
    fn size(&self) -> usize;
    fn iter(&self) -> std::slice::Iter<(F, F, F)>;

}

#[derive(Clone)]
pub struct XorTable<F: PrimeField>{
    rows: Vec<(F, F, F)>
}

impl<F: PrimeField> XorTable<F>{
    pub fn new(bit_size: usize) -> Self{
        let mut rows = vec![];
        for i in 0..bit_size{
            for j in 0..bit_size{
                let k = i ^ j;            
                let key_one = F::from_str(&j.to_string()).expect("field element");
                let key_two = F::from_str(&i.to_string()).expect("field element");
                let value = F::from_str(&k.to_string()).expect("field element");
                rows.push((key_one, key_two, value));
            }
        }
    
        let table  = XorTable{
            rows
        };

        table
    }
}
impl<F: PrimeField> LookupTable<F> for XorTable<F>{
    fn lookup_type(&self) ->TableType{
        TableType::XOR
    }
    fn lookup_type_as_fe(&self) ->F{        
        F::from_str(&TableType::XOR.to_string()).unwrap()
    }

    fn query(&self, key_one: F, key_two: F) -> Option<F> {
        match self.rows.iter().find(|(a, b, _ )| *a == key_one &&  *b == key_two){
            Some((_, _, value)) => Some(*value),
            None => None,
        }
    }

    fn size(&self) -> usize{
        self.rows.len()
    }

    fn iter(&self) -> std::slice::Iter<(F, F, F)> {
        self.rows.iter()
    }
}
#[derive(Clone)]
pub struct AndTable<F: PrimeField>{
    rows: Vec<(F, F, F)>
}

impl<F: PrimeField> AndTable<F>{
    pub fn new(bit_size: usize) -> Self{
        let mut rows = vec![];
        for i in 0..bit_size{
            for j in 0..bit_size{
                let k = i & j;            
                let key_one = F::from_str(&j.to_string()).expect("field element");
                let key_two = F::from_str(&i.to_string()).expect("field element");
                let value = F::from_str(&k.to_string()).expect("field element");
                rows.push((key_one, key_two, value));
            }
        }
    
        let table  = AndTable{
            rows
        };

        table
    }
}
impl<F: PrimeField> LookupTable<F> for AndTable<F>{
    fn lookup_type(&self) ->TableType{
        TableType::AND
    }
    fn lookup_type_as_fe(&self) ->F{        
        F::from_str(&self.lookup_type().to_string()).unwrap()
    }

    fn query(&self, key_one: F, key_two: F) -> Option<F> {
        match self.rows.iter().find(|(a, b, _ )| *a == key_one &&  *b == key_two){
            Some((_, _, value)) => Some(*value),
            None => None,
        }
    }

    fn size(&self) -> usize{
        self.rows.len()
    }

    fn iter(&self) -> std::slice::Iter<(F, F, F)> {
        self.rows.iter()
    }
}

#[test]
fn test_new_xor_table(){
    use crate::pairing::ff::{Field};
    use crate::pairing::bls12_381::Fr;

    let table = XorTable::new(4); // 4x4 table

    let one = Fr::one();
    let five = Fr::from_str("17").unwrap();

    assert_eq!(table.query(one, one), Some(Fr::zero()));
    assert_eq!(table.query(five, five), None);

    table.iter().for_each(|(key_one, key_two, value)| println!("{} {} {}", key_one, key_two, value));
}