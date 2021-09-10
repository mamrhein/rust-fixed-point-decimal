// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::Mul;

use num::One;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal,
};

// The trait One requires Mul<Self, Output = Self>. This is only satisfied for
// Decimal<0>. All other Decimal<P> are Mul<Self, Output = Decimal<P+P>. So, for
// these the corresponding functions are implemented separately.
// ???: remove these impls alltogether?
impl One for Decimal<0> {
    #[inline(always)]
    fn one() -> Self {
        Self::ONE
    }

    #[inline(always)]
    fn is_one(&self) -> bool {
        self.coeff == Self::ONE.coeff
    }
}

impl<const P: u8> Decimal<P>
where
    PrecLimitCheck<{ 0 < P }>: True,
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    #[inline(always)]
    fn one() -> Self {
        Self::ONE
    }

    #[inline(always)]
    fn is_one(&self) -> bool {
        self.coeff == Self::ONE.coeff
    }
}

impl<const P: u8, const Q: u8> Mul<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ (P + Q) <= crate::MAX_PREC }>: True,
{
    type Output = Decimal<{ P + Q }>;

    #[inline(always)]
    fn mul(self, other: Decimal<Q>) -> Self::Output {
        Self::Output::new_raw(self.coeff * other.coeff)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_one() {
        assert!(Decimal::<0>::is_one(&Decimal::<0>::one()));
        assert!(Decimal::<1>::is_one(&Decimal::<1>::one()));
        assert!(Decimal::<2>::is_one(&Decimal::<2>::one()));
        assert!(Decimal::<3>::is_one(&Decimal::<3>::one()));
        assert!(Decimal::<4>::is_one(&Decimal::<4>::one()));
        assert!(Decimal::<5>::is_one(&Decimal::<5>::one()));
        assert!(Decimal::<6>::is_one(&Decimal::<6>::one()));
        assert!(Decimal::<7>::is_one(&Decimal::<7>::one()));
        assert!(Decimal::<8>::is_one(&Decimal::<8>::one()));
        assert!(Decimal::<9>::is_one(&Decimal::<9>::one()));
    }

    #[test]
    fn test_mul_same_prec() {
        let x = Decimal::<4>::new_raw(1234567890);
        let y = x * x;
        assert_eq!(y.precision(), 8);
        assert_eq!(y.coeff, x.coeff * x.coeff);
        let z = x * Decimal::<3>::NEG_ONE;
        assert_eq!(z.precision(), 7);
        assert_eq!(z.coeff, -x.coeff * 1000);
    }

    #[test]
    fn test_mul_different_prec() {
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
    fn test_mul_pos_overflow() {
        let x = Decimal::<4>::new_raw(i128::MAX / 4 + 1);
        let _y = x * Decimal::<4>::TWO;
    }

    #[test]
    #[should_panic]
    fn test_mul_neg_overflow() {
        let x = Decimal::<2>::new_raw(i128::MIN);
        let _y = x * Decimal::<2>::NEG_ONE;
    }
}
