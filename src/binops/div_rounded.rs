// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{cmp::Ordering, ops::Div};

use rust_fixed_point_decimal_core::ten_pow;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    rounding::div_rounded,
    Decimal, DecimalError,
};

pub trait DivRounded<Rhs, Result = Self> {
    /// Returns `self` * `other`, rounded as `Result`.
    fn div_rounded(self, rhs: Rhs) -> Result;
}

impl<const P: u8, const Q: u8, const R: u8> DivRounded<Decimal<Q>, Decimal<R>>
    for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= crate::MAX_PREC }>: True,
    Decimal<P>: Div<Decimal<Q>>,
    PrecLimitCheck<{ R <= crate::MAX_PREC }>: True,
{
    #[inline(always)]
    fn div_rounded(self, other: Decimal<Q>) -> Decimal<R> {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        match P.cmp(&(Q + R)) {
            Ordering::Equal => Decimal::<R> {
                coeff: div_rounded(self.coeff, other.coeff, None),
            },
            Ordering::Less => Decimal::<R> {
                coeff: div_rounded(
                    self.coeff * ten_pow(R + Q - P),
                    other.coeff,
                    None,
                ),
            },
            Ordering::Greater => Decimal::<R> {
                coeff: div_rounded(
                    self.coeff,
                    other.coeff * ten_pow(P - Q - R),
                    None,
                ),
            },
        }
    }
}

#[cfg(test)]
mod div_decimal_tests {
    use super::*;

    #[test]
    fn test_div_rounded() {
        let x = Decimal::<0>::new_raw(17);
        let y = Decimal::<2>::new_raw(-201);
        let z: Decimal<2> = x.div_rounded(y);
        assert_eq!(z.coeff, -846);
        let x = Decimal::<8>::new_raw(17);
        let y = Decimal::<3>::new_raw(204);
        let z: Decimal<8> = x.div_rounded(y);
        assert_eq!(z.coeff, 83);
        let x = Decimal::<2>::new_raw(12345678901234567890);
        let y = Decimal::<6>::new_raw(244140625);
        let z = x / y;
        assert_eq!(z.coeff, 505679007794567900774400);
    }
}
