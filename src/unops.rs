// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::Neg;

use rust_fixed_point_decimal_core::ten_pow;

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
    ///
    /// Panics with 'attempt to negate with overflow' when called on
    /// Decimal::<P>::MIN!
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

    /// Returns the largest integral value <= `self`.
    ///
    /// Panics with 'attempt to multiply with overflow' when called on a value
    /// less than (Decimal::<P>::MIN / 10 ^ P) * 10 ^ P !
    #[inline]
    pub fn floor(&self) -> Self {
        match P {
            0 => self.clone(),
            _ => Self {
                coeff: self.coeff.div_floor(ten_pow(P)) * ten_pow(P),
            },
        }
    }

    /// Returns the smallest integral value >= `self`.
    ///
    /// Panics with 'attempt to multiply with overflow' when called on a value
    /// greater than (Decimal::<P>::MAX / 10 ^ P) * 10 ^ P !
    #[inline]
    pub fn ceil(&self) -> Self {
        match P {
            0 => self.clone(),
            _ => Self {
                coeff: self.coeff.div_ceil(ten_pow(P)) * ten_pow(P),
            },
        }
    }

    /// Returns the integer part of `self`.
    #[inline]
    pub fn trunc(&self) -> Self {
        if P == 0 {
            *self
        } else {
            Self {
                coeff: (self.coeff / ten_pow(P)) * ten_pow(P),
            }
        }
    }

    /// Returns the fractional part of `self`.
    #[inline]
    pub fn fract(&self) -> Self {
        if P == 0 {
            Self::ZERO
        } else {
            Self {
                coeff: self.coeff % ten_pow(P),
            }
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
    fn test_neg_corner_cases_ok() {
        let x = Decimal::<2>::MAX;
        let y = -x;
        assert_eq!(x.coeff, -y.coeff);
        let z = -y;
        assert_eq!(x.coeff, z.coeff);
    }

    #[test]
    #[should_panic]
    fn test_neg_corner_cases_fail() {
        let x = Decimal::<2>::MIN;
        let _y = -x;
    }

    #[test]
    fn test_abs() {
        let x = Decimal::<4>::new_raw(-123456789);
        let y = x.abs();
        assert_eq!(-x.coeff, y.coeff);
        let z = y.abs();
        assert_eq!(y.coeff, z.coeff);
    }

    #[test]
    fn test_floor() {
        let x = Decimal::<0>::new_raw(123);
        let y = x.floor();
        assert_eq!(y.coeff, x.coeff);
        let x = Decimal::<5>::new_raw(123456789);
        let y = x.floor();
        assert_eq!(y.coeff, 123400000);
        let z = y.floor();
        assert_eq!(y.coeff, z.coeff);
        let x = Decimal::<9>::new_raw(-987);
        let y = x.floor();
        assert_eq!(y.coeff, -1000000000);
        let z = y.floor();
        assert_eq!(y.coeff, z.coeff);
    }

    #[test]
    #[should_panic]
    fn test_floor_overflow() {
        let x = Decimal::<3>::new_raw((i128::MIN / 1000) * 1000 - 1);
        let _y = x.floor();
    }

    #[test]
    fn test_ceil() {
        let x = Decimal::<0>::new_raw(123);
        let y = x.ceil();
        assert_eq!(y.coeff, x.coeff);
        let x = Decimal::<5>::new_raw(123400001);
        let y = x.ceil();
        assert_eq!(y.coeff, 123500000);
        let z = y.ceil();
        assert_eq!(y.coeff, z.coeff);
        let x = Decimal::<9>::new_raw(-987);
        let y = x.ceil();
        assert_eq!(y.coeff, 0);
        let z = y.ceil();
        assert_eq!(y.coeff, z.coeff);
    }

    #[test]
    #[should_panic]
    fn test_ceil_overflow() {
        let x = Decimal::<2>::new_raw((i128::MAX / 100) * 100 + 1);
        let _y = x.ceil();
    }

    #[test]
    fn test_trunc() {
        let x = Decimal::<0>::new_raw(12345);
        let y = x.trunc();
        assert_eq!(x.coeff, y.coeff);
        let x = Decimal::<3>::new_raw(12345);
        let y = x.trunc();
        assert_eq!(y.coeff, 12000);
        let x = Decimal::<7>::new_raw(12345);
        let y = x.trunc();
        assert_eq!(y.coeff, 0);
    }

    #[test]
    fn test_fract() {
        let x = Decimal::<0>::new_raw(12345);
        let y = x.fract();
        assert_eq!(y.coeff, 0);
        let x = Decimal::<3>::new_raw(12345);
        let y = x.fract();
        assert_eq!(y.coeff, 345);
        let x = Decimal::<7>::new_raw(12345);
        let y = x.fract();
        assert_eq!(y.coeff, 12345);
    }
}
