// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::fmt;

use num::integer::div_mod_floor;
use rust_fixed_point_decimal_core::ten_pow;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

impl<const P: u8> fmt::Debug for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    fn fmt(&self, form: &mut fmt::Formatter<'_>) -> fmt::Result {
        if P == 0 {
            write!(form, "Dec!({})", self.coeff)
        } else {
            let (int, frac) = div_mod_floor(self.coeff, ten_pow(P));
            write!(form, "Dec!({}.{:0width$})", int, frac, width = P as usize)
        }
    }
}

#[cfg(test)]
mod test_fmt_debug {
    use super::*;

    #[test]
    fn test_fmt() {
        let d = Decimal::<3>::new_raw(1234567890002);
        // println!("{:?}", d);
        assert_eq!(format!("{:?}", d), "Dec!(1234567890.002)");
        let d = Decimal::<9>::new_raw(-1230000000000);
        // println!("{:?}", d);
        assert_eq!(format!("{:?}", d), "Dec!(-1230.000000000)");
        let d = Decimal::<0>::new_raw(1234567890002);
        // println!("{:?}", d);
        assert_eq!(format!("{:?}", d), "Dec!(1234567890002)");
    }
}
