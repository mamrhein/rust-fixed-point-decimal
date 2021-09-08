// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#![allow(dead_code)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(associated_type_bounds)]
#![feature(int_roundings)]

pub use errors::*;
pub use rust_fixed_point_decimal_core::{ParseDecimalError, MAX_PREC};
pub use rust_fixed_point_decimal_macros::Dec;

use crate::prec_constraints::{PrecLimitCheck, True};

mod binops;
mod errors;
mod from_decimal;
mod from_float;
mod from_int;
mod from_str;
mod rounding;
mod unops;

mod prec_constraints {
    pub trait True {}

    pub struct PrecLimitCheck<const CHECK: bool> {}

    impl True for PrecLimitCheck<true> {}
}

#[derive(Copy, Clone, Debug, Eq, Ord)]
pub struct Decimal<const P: u8>
where
    Decimal<P>: Sized,
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    coeff: i128,
}

impl<const P: u8> Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    // needs to be public because of macro Dec!
    pub fn new_raw(val: i128) -> Self {
        Decimal { coeff: val }
    }

    /// Internal representation. For debugging only!
    #[inline]
    pub fn coefficient(self) -> i128 {
        self.coeff
    }

    /// Number of fractional decimal digits
    #[inline]
    pub const fn precision(self) -> u8 {
        P
    }

    /// Additive identity
    pub const ZERO: Decimal<P> = Decimal { coeff: 0i128 };
    /// Multiplicative identity
    pub const ONE: Decimal<P> = Decimal {
        coeff: 10i128.pow(P as u32),
    };
    /// Multiplicative negator
    pub const NEG_ONE: Decimal<P> = Decimal {
        coeff: -(10i128.pow(P as u32)),
    };
    /// Equivalent of 2
    pub const TWO: Decimal<P> = Decimal {
        coeff: 2i128 * 10i128.pow(P as u32),
    };
    /// Equivalent of 10
    pub const TEN: Decimal<P> = Decimal {
        coeff: 10i128.pow((P + 1) as u32),
    };
    /// Maximum value representable by this type
    pub const MAX: Decimal<P> = Decimal { coeff: i128::MAX };
    /// Minimum value representable by this type
    pub const MIN: Decimal<P> = Decimal { coeff: i128::MIN };
    /// Smallest absolute difference between two non-equal values of this type
    pub const DELTA: Decimal<P> = Decimal { coeff: 1i128 };
}

impl<const P: u8> Default for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    /// Default value: Decimal::<P>::ZERO
    fn default() -> Self {
        Self::ZERO
    }
}

#[cfg(test)]
mod tests {
    use crate::Decimal;

    #[test]
    fn test_new_raw() {
        let val = 12345678901234567890_i128;
        let d: Decimal<5> = Decimal::new_raw(val);
        assert_eq!(d.coeff, val);
        assert_eq!(d.precision(), 5);
        let d: Decimal<9> = Decimal::new_raw(val);
        assert_eq!(d.coeff, val);
        assert_eq!(d.precision(), 9);
    }

    macro_rules! test_constants_and_default {
        () => {test_constants_and_default!(0,1,2,7,9);};
        ($($p:expr),*) => {
            #[test]
            fn test_consts() {
            $(
                assert_eq!(Decimal::<$p>::ZERO.coeff, 0i128);
                assert_eq!(Decimal::<$p>::default().coeff, 0i128);
                assert_eq!(Decimal::<$p>::ONE.coeff, 10i128.pow($p));
                assert_eq!(Decimal::<$p>::NEG_ONE.coeff,
                           Decimal::<$p>::ONE.coeff.checked_neg().unwrap());
                assert_eq!(Decimal::<$p>::TWO.coeff,
                           Decimal::<$p>::ONE.coeff * 2);
                assert_eq!(Decimal::<$p>::TEN.coeff, 10i128.pow($p + 1));
                assert_eq!(Decimal::<$p>::MAX.coeff, i128::MAX);
                assert_eq!(Decimal::<$p>::MIN.coeff, i128::MIN);
                assert_eq!(Decimal::<$p>::DELTA.coeff, 1i128);
            )*
            }
        }
    }

    test_constants_and_default!();
}
