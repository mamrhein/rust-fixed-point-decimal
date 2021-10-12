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
    Decimal, MAX_PREC,
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
        self.eq_one()
    }
}

impl<const P: u8> Decimal<P>
where
    PrecLimitCheck<{ 0 < P }>: True,
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    #[inline(always)]
    pub fn one() -> Self {
        Self::ONE
    }

    #[inline(always)]
    pub fn is_one(&self) -> bool {
        self.eq_one()
    }
}

#[cfg(test)]
mod one_tests {
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
}

pub const fn const_sum_u8(a: u8, b: u8) -> u8 {
    a + b
}

macro_rules! impl_mul_decimal {
    (impl $imp:ident, $method:ident) => {
        impl<const P: u8, const Q: u8> $imp<Decimal<Q>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ (const_sum_u8(P, Q)) <= MAX_PREC }>: True,
        {
            type Output = Decimal<{ const_sum_u8(P, Q) }>;

            #[inline(always)]
            fn mul(self, other: Decimal<Q>) -> Self::Output {
                Self::Output {
                    coeff: $imp::$method(self.coeff, other.coeff),
                }
            }
        }

        forward_ref_binop!(impl $imp, $method);
    };
}

impl_mul_decimal!(impl Mul, mul);

#[cfg(test)]
mod mul_decimal_tests {
    use super::*;

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

    #[test]
    fn test_mul_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x * y;
        assert_eq!(z.coeff, (&x * y).coeff);
        assert_eq!(z.coeff, (x * &y).coeff);
        assert_eq!(z.coeff, (&x * &y).coeff);
    }
}

macro_rules! impl_mul_decimal_and_int {
    () => {
        impl_mul_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> Mul<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<P>;

            #[inline(always)]
            fn mul(self, other: $t) -> Self::Output {
                Self::Output{
                    coeff: self.coeff * other as i128
                }
            }
        }

        impl<const P: u8> Mul<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<P>;

            #[inline(always)]
            fn mul(self, other: Decimal<P>) -> Self::Output {
                Self::Output{
                    coeff: self as i128 * other.coeff
                }
            }
        }
        )*
    }
}

impl_mul_decimal_and_int!();
forward_ref_binop_decimal_int!(impl Mul, mul);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod mul_integer_tests {
    use super::*;

    macro_rules! gen_mul_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = <$t>::MAX;
                let r = d * i;
                assert_eq!(r.precision(), d.precision());
                assert_eq!(r.coeff, i as i128 * $coeff);
                assert_eq!(r.coeff, (&d * i).coeff);
                assert_eq!(r.coeff, (d * &i).coeff);
                assert_eq!(r.coeff, (&d * &i).coeff);
                let z = i * d;
                assert_eq!(z.precision(), r.precision());
                assert_eq!(z.coeff, r.coeff);
                assert_eq!(z.coeff, (&i * d).coeff);
                assert_eq!(z.coeff, (i * &d).coeff);
                assert_eq!(z.coeff, (&i * &d).coeff);
            }
        };
    }

    gen_mul_integer_tests!(test_mul_u8, u8, 2, -1);
    gen_mul_integer_tests!(test_mul_i8, i8, 0, 123);
    gen_mul_integer_tests!(test_mul_u16, u16, 4, 11);
    gen_mul_integer_tests!(test_mul_i16, i16, 4, 1234567);
    gen_mul_integer_tests!(test_mul_u32, u32, 1, 0);
    gen_mul_integer_tests!(test_mul_i32, i32, 9, -1234);
    gen_mul_integer_tests!(test_mul_u64, u64, 3, 321);
    gen_mul_integer_tests!(test_mul_i64, i64, 7, -12345678901234567890);

    #[test]
    fn test_mul_i128() {
        let coeff = 748_i128;
        let d = Decimal::<2>::new_raw(coeff);
        let i = 12345_i128;
        let r = d * i;
        assert_eq!(r.precision(), d.precision());
        assert_eq!(r.coeff, i * coeff);
        assert_eq!(r.coeff, (&d * i).coeff);
        assert_eq!(r.coeff, (d * &i).coeff);
        assert_eq!(r.coeff, (&d * &i).coeff);
        let z = i * d;
        assert_eq!(z.precision(), r.precision());
        assert_eq!(z.coeff, r.coeff);
        assert_eq!(z.coeff, (&i * d).coeff);
        assert_eq!(z.coeff, (i * &d).coeff);
        assert_eq!(z.coeff, (&i * &d).coeff);
    }
}
