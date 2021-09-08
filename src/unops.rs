// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::Neg;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

impl<const P: u8> Neg for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    type Output = Self;

    /// Returns -self.
    fn neg(self) -> Self::Output {
        Self::Output { coeff: -self.coeff }
    }
}

impl<const P: u8> Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    /// Returns the absolute value of `self`.
    #[inline]
    pub fn abs(&self) -> Self {
        Self {
            coeff: self.coeff.abs(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Decimal;

    #[test]
    fn test_neg() {
        let val = 1234567890i128;
        let x: Decimal<2> = Decimal::new_raw(val);
        let y = -x;
        assert_eq!(x.coeff, -y.coeff);
        let z = -y;
        assert_eq!(x.coeff, z.coeff);
    }

    #[test]
    fn test_abs() {
        let x = Decimal::<4>::new_raw(-123456789);
        let y = x.abs();
        assert_eq!(-x.coeff, y.coeff);
        let z = y.abs();
        assert_eq!(y.coeff, z.coeff);
    }
}
