// #![feature(core_intrinsics)]

#![allow(unused_imports)]
#![allow(unused_macros)]
#![allow(dead_code)]
#[macro_use]

extern crate cfg_if;
pub extern crate pairing;
extern crate rand;
extern crate bit_vec;
extern crate byteorder;

pub use pairing::*;

use crate::pairing::ff as ff;
pub use ff::*;

#[macro_use]
mod log;

pub mod domain;
pub mod groth16;

#[cfg(feature = "gm17")]
pub mod gm17;

#[cfg(feature = "sonic")]
pub mod sonic;

#[cfg(feature = "plonk")]
pub mod plonk;
#[macro_use]
extern crate lazy_static;
pub mod marlin;

mod group;
mod source;
mod multiexp;

#[cfg(test)]
mod tests;

cfg_if! {
    if #[cfg(feature = "multicore")] {
        #[cfg(feature = "wasm")]
        compile_error!("Multicore feature is not yet compatible with wasm target arch");

        mod multicore;
        mod worker {
            pub use crate::multicore::*;
        }
    } else {
        mod singlecore;
        mod worker {
            pub use crate::singlecore::*;
        }
    }
}

mod cs;
pub use self::cs::*;

use std::str::FromStr;
use std::env;

fn verbose_flag() -> bool {
    option_env!("BELLMAN_VERBOSE").unwrap_or("0") == "1"
}