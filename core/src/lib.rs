// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

mod parser;
mod powers_of_ten;

pub const MAX_PREC: u8 = 9;

pub use parser::{dec_repr_from_str, ParseDecimalError};
pub use powers_of_ten::{checked_mul_pow_ten, ten_pow};
