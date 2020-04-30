use crate::pairing::Engine;
use crate::pairing::ff::PrimeField;
use std::fmt;

#[derive(Clone, Eq)]
pub enum TableType{
    XOR = 1,
    AND = 2,
    Range = 3,
}

impl fmt::Display for TableType{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { 
        let type_as_int = match self{
            Self::XOR => 1,
            Self::AND => 2,
            Self::Range => 3,
        };
        write!(f, "{}", type_as_int)
     }
}

impl PartialEq for TableType{
    fn eq(&self, other: &TableType) -> bool {
        match (self, other){
            (TableType::XOR, TableType::XOR) |
            (TableType::AND, TableType::AND) |
            (TableType::Range, TableType::Range) => true,
            _ => false,
        }
    }
}




pub trait LookupTable<F: PrimeField>{
    fn lookup_type(&self) -> TableType;
    fn lookup_table_type_as_fe(&self) -> F;
    fn query(&self, _: F, _: F) -> Option<F>;
    fn query_generic(&self, elems: Vec<F>) -> Option<Vec<F>>;
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
    
    fn lookup_table_type_as_fe(&self) ->F{        
        F::from_str(&TableType::XOR.to_string()).unwrap()
    }

    fn query(&self, key_one: F, key_two: F) -> Option<F> {
        match self.rows.iter().find(|(a, b, _ )| *a == key_one &&  *b == key_two){
            Some((_, _, value)) => Some(*value),
            None => None,
        }
    }

    fn query_generic(&self, elems: Vec<F>) -> Option<Vec<F>>{
        assert_eq!(elems.len(), 2, "only two keys allowed");
        
        match self.query(elems[0], elems[1]){
            Some(result) => Some(vec![result]),
            None => None
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
    fn lookup_table_type_as_fe(&self) ->F{        
        F::from_str(&self.lookup_type().to_string()).unwrap()
    }

    fn query(&self, key_one: F, key_two: F) -> Option<F> {
        match self.rows.iter().find(|(a, b, _ )| *a == key_one &&  *b == key_two){
            Some((_, _, value)) => Some(*value),
            None => None,
        }
    }

    fn query_generic(&self, elems: Vec<F>) -> Option<Vec<F>>{
        assert_eq!(elems.len(), 2, "only two keys allowed");
            
        match self.query(elems[0], elems[1]){
            Some(result) => Some(vec![result]),
            None => None
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
pub struct RangeTable<F: PrimeField>{
    rows: Vec<(F, F, F)>,
}

impl<F: PrimeField> RangeTable<F>{
    pub fn new(size: usize) -> Self{
        let mut rows = vec![];
        // let mut rows = Vec::<F>::new();
        let zero = F::zero();

        for i in (0..size).into_iter(){
            let elem = F::from_str(&format!("{}", i)).unwrap();

            rows.push((elem, zero ,zero));
        }

        Self{
            rows
        }
    }
}

impl<F: PrimeField> LookupTable<F> for RangeTable<F>{

    fn query(&self, a: F, _: F) -> Option<F> { 
        match self.rows.iter().find(|(e, _, _)| *e == a){
            Some((value, _, _)) => Some(*value),
            None => None,
        }
    }

    fn lookup_type(&self) ->TableType{
        TableType::Range
    }
    fn lookup_table_type_as_fe(&self) ->F{        
        F::from_str(&self.lookup_type().to_string()).unwrap()
    }

    fn query_generic(&self, elems: Vec<F>) -> Option<Vec<F>>{
        unimplemented!()
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

#[test]
fn test_new_range_table(){
    use crate::pairing::ff::{Field};
    use crate::pairing::bls12_381::Fr;

    let table = RangeTable::new(1<<4); // 4x4 table

    let one = Fr::one();
    let seventeen = Fr::from_str("17").unwrap();

    assert_eq!(table.query(one, Fr::zero()), Some(Fr::one()));
    assert_eq!(table.query(seventeen, Fr::zero()), None);

    table.iter().for_each(|(elem, _, _ )| println!(" {}", elem));
}