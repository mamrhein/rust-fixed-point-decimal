// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use crate::{
    binops::const_sum_u8,
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

pub trait CheckedMul<Rhs = Self> {
    type Output;
    fn checked_mul(self, rhs: Rhs) -> Self::Output;
}

impl<const P: u8, const Q: u8> CheckedMul<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
    PrecLimitCheck<{ (const_sum_u8(P, Q)) <= MAX_PREC }>: True,
{
    type Output = Option<Decimal<{ const_sum_u8(P, Q) }>>;

    #[inline(always)]
    fn checked_mul(self, other: Decimal<Q>) -> Self::Output {
        match i128::checked_mul(self.coeff, other.coeff) {
            Some(coeff) => Some(Decimal { coeff: coeff }),
            None => None,
        }
    }
}

forward_ref_binop!(impl CheckedMul, checked_mul);

#[cfg(test)]
mod checked_mul_decimal_tests {
    use super::*;

    #[test]
    fn test_checked_mul() {
        let x = Decimal::<4>::new_raw(1234567890);
        let y = x.checked_mul(x).unwrap();
        assert_eq!(y.coeff, x.coeff * x.coeff);
        let z = x.checked_mul(Decimal::<4>::NEG_ONE).unwrap();
        assert_eq!(z.coeff, -x.coeff * 10000);
        let x = Decimal::<5>::new_raw(1234567890);
        let y = Decimal::<1>::new_raw(890);
        let z = x.checked_mul(y).unwrap();
        assert_eq!(z.coeff, x.coeff * y.coeff);
        let z = y.checked_mul(x).unwrap();
        assert_eq!(z.coeff, x.coeff * y.coeff);
        let z = x.checked_mul(Decimal::<3>::NEG_ONE).unwrap();
        assert_eq!(z.coeff, -x.coeff * 1000);
    }

    #[test]
    fn test_checked_mul_pos_overflow() {
        let x = Decimal::<4>::new_raw(i128::MAX / 4 + 1);
        let y = x.checked_mul(Decimal::<4>::TWO);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_mul_neg_overflow() {
        let x = Decimal::<2>::new_raw(i128::MIN);
        let y = x.checked_mul(Decimal::<2>::NEG_ONE);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_mul_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x.checked_mul(y).unwrap();
        assert_eq!(z.coeff, (&x).checked_mul(y).unwrap().coeff);
        assert_eq!(z.coeff, x.checked_mul(&y).unwrap().coeff);
        assert_eq!(z.coeff, (&x).checked_mul(&y).unwrap().coeff);
    }
}

macro_rules! impl_checked_mul_decimal_and_int {
    () => {
        impl_checked_mul_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> CheckedMul<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<P>>;

            #[inline(always)]
            fn checked_mul(self, other: $t) -> Self::Output {
                match i128::checked_mul(self.coeff, other as i128) {
                    Some(coeff) => Some(Decimal { coeff: coeff }),
                    None => None,
                }
            }
        }

        impl<const P: u8> CheckedMul<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<P>>;

            #[inline(always)]
            fn checked_mul(self, other: Decimal<P>) -> Self::Output {
                match i128::checked_mul(self as i128, other.coeff) {
                    Some(coeff) => Some(Decimal { coeff: coeff }),
                    None => None,
                }
            }
        }
        )*
    }
}

impl_checked_mul_decimal_and_int!();
forward_ref_binop_decimal_int!(impl CheckedMul, checked_mul);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod checked_mul_integer_tests {
    use super::*;

    macro_rules! gen_checked_mul_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = <$t>::MAX;
                let r = d.checked_mul(i).unwrap();
                assert_eq!(r.coeff, i as i128 * $coeff);
                assert_eq!(r.coeff, (&d).checked_mul(i).unwrap().coeff);
                assert_eq!(r.coeff, d.checked_mul(&i).unwrap().coeff);
                assert_eq!(r.coeff, (&d).checked_mul(&i).unwrap().coeff);
                let z = CheckedMul::checked_mul(i, d).unwrap();
                assert_eq!(z.coeff, r.coeff);
                assert_eq!(
                    z.coeff,
                    CheckedMul::checked_mul(&i, d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedMul::checked_mul(i, &d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedMul::checked_mul(&i, &d).unwrap().coeff
                );
                let d = Decimal::<$p>::MAX;
                let i: $t = 2;
                let z = d.checked_mul(i);
                assert!(z.is_none());
            }
        };
    }

    gen_checked_mul_integer_tests!(test_checked_mul_u8, u8, 2, -1);
    gen_checked_mul_integer_tests!(test_checked_mul_i8, i8, 0, 123);
    gen_checked_mul_integer_tests!(test_checked_mul_u16, u16, 4, 11);
    gen_checked_mul_integer_tests!(test_checked_mul_i16, i16, 4, 1234567);
    gen_checked_mul_integer_tests!(test_checked_mul_u32, u32, 1, 0);
    gen_checked_mul_integer_tests!(test_checked_mul_i32, i32, 9, -1234);
    gen_checked_mul_integer_tests!(test_checked_mul_u64, u64, 3, 321);
    gen_checked_mul_integer_tests!(
        test_checked_mul_i64,
        i64,
        7,
        -12345678901234567890
    );

    #[test]
    fn test_checked_mul_i128() {
        let coeff = 748_i128;
        let d = Decimal::<2>::new_raw(coeff);
        let i = 12345_i128;
        let r = d.checked_mul(i).unwrap();
        assert_eq!(r.coeff, i as i128 * coeff);
        assert_eq!(r.coeff, (&d).checked_mul(i).unwrap().coeff);
        assert_eq!(r.coeff, d.checked_mul(&i).unwrap().coeff);
        assert_eq!(r.coeff, (&d).checked_mul(&i).unwrap().coeff);
        let z = CheckedMul::checked_mul(i, d).unwrap();
        assert_eq!(z.coeff, r.coeff);
        assert_eq!(z.coeff, CheckedMul::checked_mul(&i, d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedMul::checked_mul(i, &d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedMul::checked_mul(&i, &d).unwrap().coeff);
        let i = u64::MAX as i128;
        let d = Decimal::<3>::new_raw(i);
        let z = d.checked_mul(i);
        assert!(z.is_none());
    }
}
