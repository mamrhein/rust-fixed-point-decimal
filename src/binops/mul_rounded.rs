// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{cmp::Ordering, ops::Mul};

use rust_fixed_point_decimal_core::ten_pow;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    rounding::div_rounded,
    Decimal, MAX_PREC,
};

pub trait MulRounded<Rhs, Result = Self> {
    /// Returns `self` * `other`, rounded as `Result`.
    fn mul_rounded(self, rhs: Rhs) -> Result;
}

impl<const P: u8, const Q: u8, const R: u8> MulRounded<Decimal<Q>, Decimal<R>>
    for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
    Decimal<P>: Mul<Decimal<Q>>,
    PrecLimitCheck<{ R <= MAX_PREC }>: True,
{
    #[inline(always)]
    fn mul_rounded(self, other: Decimal<Q>) -> Decimal<R> {
        match R.cmp(&(P + Q)) {
            Ordering::Equal => Decimal::<R> {
                coeff: self.coeff * other.coeff,
            },
            Ordering::Less => Decimal::<R> {
                coeff: div_rounded(
                    self.coeff * other.coeff,
                    ten_pow(P + Q - R),
                    None,
                ),
            },
            Ordering::Greater => Decimal::<R> {
                coeff: self.coeff * other.coeff * ten_pow(R - P - Q),
            },
        }
    }
}

forward_ref_binop_rounded!(impl MulRounded, mul_rounded);

#[cfg(test)]
mod mul_rounded_decimal_tests {
    use super::*;

    #[test]
    fn test_mul_rounded_less_prec() {
        let x = Decimal::<2>::new_raw(12345);
        let z: Decimal<2> = x.mul_rounded(x);
        assert_eq!(z.coeff, 1523990);
        let y = Decimal::<4>::new_raw(5781);
        let z: Decimal<1> = x.mul_rounded(y);
        assert_eq!(z.coeff, 714);
        let z: Decimal<1> = y.mul_rounded(x);
        assert_eq!(z.coeff, 714);
    }

    #[test]
    fn test_mul_rounded_no_adj_needed() {
        let x = Decimal::<2>::new_raw(12345);
        let z: Decimal<4> = x.mul_rounded(x);
        assert_eq!(z.coeff, 152399025);
        let y = Decimal::<4>::new_raw(5781);
        let z: Decimal<6> = x.mul_rounded(y);
        assert_eq!(z.coeff, 71366445);
        let z: Decimal<6> = y.mul_rounded(x);
        assert_eq!(z.coeff, 71366445);
    }

    #[test]
    fn test_mul_rounded_greater_prec() {
        let x = Decimal::<2>::new_raw(12345);
        let z: Decimal<6> = x.mul_rounded(x);
        assert_eq!(z.coeff, 15239902500);
        let y = Decimal::<4>::new_raw(5781);
        let z: Decimal<7> = x.mul_rounded(y);
        assert_eq!(z.coeff, 713664450);
        let z: Decimal<9> = y.mul_rounded(x);
        assert_eq!(z.coeff, 71366445000);
    }

    #[test]
    fn test_mul_rounded_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z: Decimal<2> = x.mul_rounded(y);
        let a: Decimal<2> = MulRounded::mul_rounded(&x, y);
        assert_eq!(a.coeff, z.coeff);
        let a: Decimal<2> = MulRounded::mul_rounded(x, &y);
        assert_eq!(a.coeff, z.coeff);
        let a: Decimal<2> = MulRounded::mul_rounded(&x, &y);
        assert_eq!(a.coeff, z.coeff);
    }
}
