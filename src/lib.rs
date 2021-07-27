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
#![feature(const_generics)]
#![feature(const_evaluatable_checked)]
#![feature(associated_type_bounds)]

mod powers_of_ten;

pub const MAX_PREC: u8 = 30;

pub(crate) trait True {}

pub(crate) struct PrecLimitCheck<const CHECK: bool> {}

impl True for PrecLimitCheck<true> {}

#[derive(Copy, Clone, Debug)]
pub(crate) struct Decimal<const P: u8>
    where
        Decimal<P>: Sized,
        PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    coeff: i128,
}

impl<const P: u8> Decimal<P>
    where
        PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    fn new_raw(val: i128) -> Self {
        Decimal { coeff: val }
    }

    #[inline]
    const fn precision(self) -> u8 {
        P
    }

    pub const ZERO: Decimal<P> = Decimal { coeff: 0i128 };
    pub const ONE: Decimal<P> = Decimal { coeff: 10i128.pow(P as u32) };
    pub const NEG_ONE: Decimal<P> = Decimal { coeff: -(10i128.pow(P as u32))};
    pub const TWO: Decimal<P> = Decimal { coeff: 2i128 * 10i128.pow(P as u32) };
    pub const TEN: Decimal<P> = Decimal { coeff: 10i128.pow((P + 1) as u32) };
}

impl<const P: u8> Default for Decimal<P>
    where
        PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
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
        let d: Decimal<30> = Decimal::new_raw(val);
        assert_eq!(d.coeff, val);
        assert_eq!(d.precision(), 30);
    }

    macro_rules! test_constants_and_default {
        () => {test_constants_and_default!(0,1,2,17,30);};
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
            )*
            }
        }
    }

    test_constants_and_default!();
}
