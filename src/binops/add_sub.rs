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
    ops::{Add, AddAssign, Sub, SubAssign},
};

use num::Zero;
use rust_fixed_point_decimal_core::mul_pow_ten;

use crate::{
    binops::const_max_u8,
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

impl<const P: u8> Zero for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    Decimal<P>: Add<Output = Decimal<P>>,
{
    #[inline(always)]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.coeff.is_zero()
    }
}

#[cfg(test)]
mod zero_tests {
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
}

macro_rules! impl_add_sub_decimal {
    (impl $imp:ident, $method:ident) => {
        impl<const P: u8, const Q: u8> $imp<Decimal<Q>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ const_max_u8(P, Q) <= MAX_PREC }>: True,
        {
            type Output = Decimal<{ const_max_u8(P, Q) }>;

            #[inline(always)]
            fn $method(self, other: Decimal<Q>) -> Self::Output {
                match P.cmp(&Q) {
                    Ordering::Equal => Self::Output {
                        coeff: $imp::$method(self.coeff, other.coeff),
                    },
                    Ordering::Greater => Self::Output {
                        coeff: $imp::$method(
                            self.coeff,
                            mul_pow_ten(other.coeff, P - Q),
                        ),
                    },
                    Ordering::Less => Self::Output {
                        coeff: $imp::$method(
                            mul_pow_ten(self.coeff, Q - P),
                            other.coeff,
                        ),
                    },
                }
            }
        }

        forward_ref_binop!(impl $imp, $method);
    };
}

impl_add_sub_decimal!(impl Add, add);

impl_add_sub_decimal!(impl Sub, sub);

#[cfg(test)]
mod add_sub_decimal_tests {
    use super::*;

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
    #[allow(clippy::eq_op)]
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

    #[test]
    fn test_add_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x + y;
        assert_eq!(z.coeff, (&x + y).coeff);
        assert_eq!(z.coeff, (x + &y).coeff);
        assert_eq!(z.coeff, (&x + &y).coeff);
    }

    #[test]
    fn test_sub_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x - y;
        assert_eq!(z.coeff, (&x - y).coeff);
        assert_eq!(z.coeff, (x - &y).coeff);
        assert_eq!(z.coeff, (&x - &y).coeff);
    }
}

macro_rules! impl_add_sub_decimal_and_int {
    (impl $imp:ident, $method:ident) => {
        impl_add_sub_decimal_and_int!(
            impl $imp, $method, u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    (impl $imp:ident, $method:ident, $($t:ty),*) => {
        $(
        impl<const P: u8> $imp<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<P>;

            #[inline(always)]
            fn $method(self, other: $t) -> Self::Output {
                if P == 0 {
                    Self::Output{
                        coeff: $imp::$method(self.coeff, other as i128)
                    }
                } else {
                    Self::Output{
                        coeff: $imp::$method(self.coeff,
                                             mul_pow_ten(other as i128, P))
                    }
                }
            }
        }

        impl<const P: u8> $imp<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<P>;

            #[inline(always)]
            fn $method(self, other: Decimal<P>) -> Self::Output {
                if P == 0 {
                    Self::Output{
                        coeff: $imp::$method(self as i128, other.coeff)
                    }
                } else {
                    Self::Output{
                        coeff: $imp::$method(mul_pow_ten(self as i128, P),
                                             other.coeff)
                    }
                }
            }
        }
        )*
    }
}

impl_add_sub_decimal_and_int!(impl Add, add);
forward_ref_binop_decimal_int!(impl Add, add);

impl_add_sub_decimal_and_int!(impl Sub, sub);
forward_ref_binop_decimal_int!(impl Sub, sub);

#[cfg(test)]
mod add_sub_integer_tests {
    use rust_fixed_point_decimal_core::ten_pow;

    use super::*;

    macro_rules! gen_add_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = <$t>::MAX;
                let r = d + i;
                assert_eq!(r.precision(), d.precision());
                assert_eq!(r.coeff, i as i128 * ten_pow($p) + $coeff);
                assert_eq!(r.coeff, (&d + i).coeff);
                assert_eq!(r.coeff, (d + &i).coeff);
                assert_eq!(r.coeff, (&d + &i).coeff);
                let z = i + d;
                assert_eq!(z.precision(), r.precision());
                assert_eq!(z.coeff, r.coeff);
                assert_eq!(z.coeff, (&i + d).coeff);
                assert_eq!(z.coeff, (i + &d).coeff);
                assert_eq!(z.coeff, (&i + &d).coeff);
            }
        };
    }

    gen_add_integer_tests!(test_add_u8, u8, 2, 1);
    gen_add_integer_tests!(test_add_i8, i8, 0, 123);
    gen_add_integer_tests!(test_add_u16, u16, 4, 11);
    gen_add_integer_tests!(test_add_i16, i16, 4, 1234567);
    gen_add_integer_tests!(test_add_u32, u32, 1, 0);
    gen_add_integer_tests!(test_add_i32, i32, 9, 1234);
    gen_add_integer_tests!(test_add_u64, u64, 3, 321);
    gen_add_integer_tests!(test_add_i64, i64, 7, 12345678901234567890);

    #[test]
    fn test_add_i128() {
        let d = Decimal::<2>::new_raw(1);
        let i = 12345_i128;
        let r = d + i;
        assert_eq!(r.coeff, i * 100 + 1);
        assert_eq!(r.coeff, (&d + i).coeff);
        assert_eq!(r.coeff, (d + &i).coeff);
        assert_eq!(r.coeff, (&d + &i).coeff);
        let z = i + d;
        assert_eq!(z.precision(), r.precision());
        assert_eq!(z.coeff, r.coeff);
        assert_eq!(z.coeff, (&i + d).coeff);
        assert_eq!(z.coeff, (i + &d).coeff);
        assert_eq!(z.coeff, (&i + &d).coeff);
    }

    macro_rules! gen_sub_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = <$t>::MAX;
                let r = d - i;
                assert_eq!(r.precision(), d.precision());
                assert_eq!(r.coeff, $coeff - i as i128 * ten_pow($p));
                assert_eq!(r.coeff, (&d - i).coeff);
                assert_eq!(r.coeff, (d - &i).coeff);
                assert_eq!(r.coeff, (&d - &i).coeff);
                let z = i - d;
                assert_eq!(z.precision(), r.precision());
                assert_eq!(z.coeff, i as i128 * ten_pow($p) - $coeff);
                assert_eq!(z.coeff, (&i - d).coeff);
                assert_eq!(z.coeff, (i - &d).coeff);
                assert_eq!(z.coeff, (&i - &d).coeff);
            }
        };
    }

    gen_sub_integer_tests!(test_sub_u8, u8, 2, 1);
    gen_sub_integer_tests!(test_sub_i8, i8, 0, 123);
    gen_sub_integer_tests!(test_sub_u16, u16, 4, 11);
    gen_sub_integer_tests!(test_sub_i16, i16, 4, 1234567);
    gen_sub_integer_tests!(test_sub_u32, u32, 1, 0);
    gen_sub_integer_tests!(test_sub_i32, i32, 9, 1234);
    gen_sub_integer_tests!(test_sub_u64, u64, 3, 321);
    gen_sub_integer_tests!(test_sub_i64, i64, 7, 12345678901234567890);

    #[test]
    fn test_sub_i128() {
        let d = Decimal::<2>::new_raw(501);
        let i = 12345_i128;
        let r = d - i;
        assert_eq!(r.coeff, -i * 100 + 501);
        assert_eq!(r.coeff, (&d - i).coeff);
        assert_eq!(r.coeff, (d - &i).coeff);
        assert_eq!(r.coeff, (&d - &i).coeff);
        let z = i - d;
        assert_eq!(z.coeff, i * 100 - 501);
        assert_eq!(z.coeff, (&i - d).coeff);
        assert_eq!(z.coeff, (i - &d).coeff);
        assert_eq!(z.coeff, (&i - &d).coeff);
    }
}
