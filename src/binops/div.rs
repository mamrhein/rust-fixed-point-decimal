// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::Div;

use num::integer::div_mod_floor;
use rust_fixed_point_decimal_core::mul_pow_ten;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal, DecimalError, MAX_PREC,
};

impl<const P: u8, const Q: u8> Div<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
{
    type Output = Decimal<9>;

    fn div(self, other: Decimal<Q>) -> Self::Output {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        if other.eq_one() {
            return Self::Output {
                coeff: mul_pow_ten(self.coeff, MAX_PREC - P),
            };
        }
        let r = MAX_PREC + Q - P;
        let (quot, rem) =
            div_mod_floor(mul_pow_ten(self.coeff, r), other.coeff);
        if rem != 0 {
            panic!("{}", DecimalError::PrecLimitExceeded);
        }
        Self::Output { coeff: quot }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div() {
        let x = Decimal::<0>::new_raw(17);
        let y = Decimal::<2>::new_raw(-200);
        let z = x / y;
        assert_eq!(z.coeff, -8500000000);
        let x = Decimal::<8>::new_raw(17);
        let y = Decimal::<0>::new_raw(2);
        let z = x / y;
        assert_eq!(z.coeff, 85);
        let x = Decimal::<2>::new_raw(12345678901234567890);
        let y = Decimal::<6>::new_raw(244140625);
        let z = x / y;
        assert_eq!(z.coeff, 505679007794567900774400);
    }

    #[test]
    fn test_div_by_one() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ONE;
        let z = x / y;
        assert_eq!(z.coeff, 170000);
        let y = Decimal::<9>::ONE;
        let z = x / y;
        assert_eq!(z.coeff, 170000);
    }

    #[test]
    #[should_panic]
    fn test_div_by_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ZERO;
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_prec_limit_exceeded() {
        let x = Decimal::<9>::new_raw(17);
        let y = Decimal::<0>::new_raw(2);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_overflow() {
        let x = Decimal::<0>::new_raw(mul_pow_ten(17, 20));
        let y = Decimal::<9>::new_raw(2);
        let _z = x / y;
    }
}
