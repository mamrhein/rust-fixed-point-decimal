// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{
    cmp::Ordering,
    ops::{Add, Sub},
};

use num::Zero;
use rust_fixed_point_decimal_core::mul_pow_ten;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal,
};

pub const fn const_max_u8(a: u8, b: u8) -> u8 {
    if a > b {
        a
    } else {
        b
    }
}

impl<const P: u8> Zero for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
    Decimal<P>: Add<Output = Decimal<P>>,
{
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool {
        self.coeff.is_zero()
    }
}

impl<const P: u8, const Q: u8> Add<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ const_max_u8(P, Q) <= crate::MAX_PREC }>: True,
{
    type Output = Decimal<{ const_max_u8(P, Q) }>;

    fn add(self, other: Decimal<Q>) -> Self::Output {
        let res_val = match P.cmp(&Q) {
            Ordering::Equal => self.coeff + other.coeff,
            Ordering::Greater => self.coeff + mul_pow_ten(other.coeff, P - Q),
            Ordering::Less => mul_pow_ten(self.coeff, Q - P) + other.coeff,
        };
        Self::Output::new_raw(res_val)
    }
}

impl<const P: u8, const Q: u8> Sub<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ const_max_u8(P, Q) <= crate::MAX_PREC }>: True,
{
    type Output = Decimal<{ const_max_u8(P, Q) }>;

    fn sub(self, other: Decimal<Q>) -> Self::Output {
        let res_val = match P.cmp(&Q) {
            Ordering::Equal => self.coeff - other.coeff,
            Ordering::Greater => self.coeff - mul_pow_ten(other.coeff, P - Q),
            Ordering::Less => mul_pow_ten(self.coeff, Q - P) - other.coeff,
        };
        Self::Output::new_raw(res_val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero() {
        assert!(Decimal::<0>::is_zero(&Decimal::<0>::zero()));
        assert!(Decimal::<1>::is_zero(&Decimal::<1>::zero()));
        assert!(Decimal::<2>::is_zero(&Decimal::<2>::zero()));
        assert!(Decimal::<3>::is_zero(&Decimal::<3>::zero()));
        assert!(Decimal::<4>::is_zero(&Decimal::<4>::zero()));
        assert!(Decimal::<5>::is_zero(&Decimal::<5>::zero()));
        assert!(Decimal::<6>::is_zero(&Decimal::<6>::zero()));
        assert!(Decimal::<7>::is_zero(&Decimal::<7>::zero()));
        assert!(Decimal::<8>::is_zero(&Decimal::<8>::zero()));
        assert!(Decimal::<9>::is_zero(&Decimal::<9>::zero()));
    }

    #[test]
    fn test_add_same_prec() {
        let x = Decimal::<3>::new_raw(1234567890);
        let y = x + x;
        assert_eq!(y.coeff, 2 * x.coeff);
        let z = x + Decimal::<3>::NEG_ONE;
        assert_eq!(z.coeff, x.coeff - 1000);
    }

    #[test]
    fn test_add_different_prec() {
        let x = Decimal::<5>::new_raw(1234567890);
        let y = Decimal::<1>::new_raw(890);
        let z = x + y;
        assert_eq!(z.coeff, x.coeff + y.coeff * 10000);
        let z = y + x;
        assert_eq!(z.coeff, x.coeff + y.coeff * 10000);
        let z = x + Decimal::<3>::NEG_ONE;
        assert_eq!(z.coeff, x.coeff - Decimal::<5>::ONE.coeff);
    }

    #[test]
    #[should_panic]
    fn test_add_pos_overflow() {
        let x = Decimal::<4>::new_raw(i128::MAX - 19999);
        let _y = x + Decimal::<4>::TWO;
    }

    #[test]
    #[should_panic]
    fn test_add_neg_overflow() {
        let x = Decimal::<2>::new_raw(i128::MIN + 99);
        let _y = x + Decimal::<2>::NEG_ONE;
    }

    #[test]
    fn test_sub_same_prec() {
        let x = Decimal::<3>::new_raw(1234567890);
        let y = x - x;
        assert_eq!(y.coeff, 0);
        let z = x - Decimal::<3>::NEG_ONE;
        assert_eq!(z.coeff, x.coeff + 1000);
    }

    #[test]
    fn test_sub_different_prec() {
        let x = Decimal::<2>::new_raw(1234567890);
        let y = Decimal::<1>::new_raw(890);
        let z = x - y;
        assert_eq!(z.coeff, x.coeff - y.coeff * 10);
        let z = y - x;
        assert_eq!(z.coeff, y.coeff * 10 - x.coeff);
        let z = x - Decimal::<3>::NEG_ONE;
        assert_eq!(z.coeff, x.coeff * 10 + Decimal::<3>::ONE.coeff);
    }

    #[test]
    #[should_panic]
    fn test_sub_pos_overflow() {
        let x = Decimal::<0>::new_raw(i128::MIN + 10);
        let _y = Decimal::<0>::TEN - x;
    }

    #[test]
    #[should_panic]
    fn test_sub_neg_overflow() {
        let x = Decimal::<4>::new_raw(i128::MIN + 99999);
        let _y = x - Decimal::<4>::TEN;
    }
}
