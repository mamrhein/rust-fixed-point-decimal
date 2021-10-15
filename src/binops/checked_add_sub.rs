// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::cmp::Ordering;

use rust_fixed_point_decimal_core::mul_pow_ten;

use crate::{
    binops::const_max_u8,
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

pub trait CheckedAdd<Rhs = Self> {
    type Output;
    fn checked_add(self, rhs: Rhs) -> Self::Output;
}

pub trait CheckedSub<Rhs = Self> {
    type Output;
    fn checked_sub(self, rhs: Rhs) -> Self::Output;
}

macro_rules! impl_checked_add_sub_decimal {
    (impl $imp:ident, $method:ident) => {
        impl<const P: u8, const Q: u8> $imp<Decimal<Q>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ const_max_u8(P, Q) <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<{ const_max_u8(P, Q) }>>;

            #[inline(always)]
            fn $method(self, other: Decimal<Q>) -> Self::Output {
                let coeff = match P.cmp(&Q) {
                    Ordering::Equal => i128::$method(self.coeff, other.coeff),
                    Ordering::Greater => i128::$method(
                        self.coeff,
                        mul_pow_ten(other.coeff, P - Q),
                    ),
                    Ordering::Less => i128::$method(
                        mul_pow_ten(self.coeff, Q - P),
                        other.coeff,
                    ),
                }?;
                Some(Decimal { coeff: coeff })
            }
        }

        forward_ref_binop!(impl $imp, $method);
    };
}

impl_checked_add_sub_decimal!(impl CheckedAdd, checked_add);

impl_checked_add_sub_decimal!(impl CheckedSub, checked_sub);

#[cfg(test)]
mod checked_add_sub_decimal_tests {
    use super::*;

    #[test]
    fn test_checked_add() {
        let x = Decimal::<3>::new_raw(1234567890);
        let y = x.checked_add(x).unwrap();
        assert_eq!(y.coeff, 2 * x.coeff);
        let z = x.checked_add(Decimal::<3>::NEG_ONE).unwrap();
        assert_eq!(z.coeff, x.coeff - 1000);
        let x = Decimal::<5>::new_raw(1234567890);
        let y = Decimal::<1>::new_raw(890);
        let z = x.checked_add(y).unwrap();
        assert_eq!(z.coeff, x.coeff + y.coeff * 10000);
        let z = y.checked_add(x).unwrap();
        assert_eq!(z.coeff, x.coeff + y.coeff * 10000);
        let z = x.checked_add(Decimal::<3>::NEG_ONE).unwrap();
        assert_eq!(z.coeff, x.coeff - Decimal::<5>::ONE.coeff);
    }

    #[test]
    fn test_checked_add_pos_overflow() {
        let x = Decimal::<4>::new_raw(i128::MAX - 19999);
        let y = x.checked_add(Decimal::<4>::TWO);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_add_neg_overflow() {
        let x = Decimal::<2>::new_raw(i128::MIN + 99);
        let y = x.checked_add(Decimal::<2>::NEG_ONE);
        assert!(y.is_none());
    }

    #[test]
    #[allow(clippy::eq_op)]
    fn test_checked_sub() {
        let x = Decimal::<3>::new_raw(1234567890);
        let y = x.checked_sub(x).unwrap();
        assert_eq!(y.coeff, 0);
        let z = x.checked_sub(Decimal::<3>::NEG_ONE).unwrap();
        assert_eq!(z.coeff, x.coeff + 1000);
        let x = Decimal::<2>::new_raw(1234567890);
        let y = Decimal::<1>::new_raw(890);
        let z = x.checked_sub(y).unwrap();
        assert_eq!(z.coeff, x.coeff - y.coeff * 10);
        let z = y.checked_sub(x).unwrap();
        assert_eq!(z.coeff, y.coeff * 10 - x.coeff);
        let z = x.checked_sub(Decimal::<3>::NEG_ONE).unwrap();
        assert_eq!(z.coeff, x.coeff * 10 + Decimal::<3>::ONE.coeff);
    }

    #[test]
    fn test_checked_sub_pos_overflow() {
        let x = Decimal::<0>::new_raw(i128::MIN + 10);
        let y = Decimal::<0>::TEN.checked_sub(x);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_sub_neg_overflow() {
        let x = Decimal::<4>::new_raw(i128::MIN + 99999);
        let y = x.checked_sub(Decimal::<4>::TEN);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_add_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x.checked_add(y).unwrap();
        assert_eq!(z.coeff, (&x).checked_add(y).unwrap().coeff);
        assert_eq!(z.coeff, x.checked_add(&y).unwrap().coeff);
        assert_eq!(z.coeff, (&x).checked_add(&y).unwrap().coeff);
    }

    #[test]
    fn test_checked_sub_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x.checked_sub(y).unwrap();
        assert_eq!(z.coeff, (&x).checked_sub(y).unwrap().coeff);
        assert_eq!(z.coeff, x.checked_sub(&y).unwrap().coeff);
        assert_eq!(z.coeff, (&x).checked_sub(&y).unwrap().coeff);
    }
}

macro_rules! impl_checked_add_sub_decimal_and_int {
    (impl $imp:ident, $method:ident) => {
        impl_checked_add_sub_decimal_and_int!(
            impl $imp, $method, u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    (impl $imp:ident, $method:ident, $($t:ty),*) => {
        $(
        impl<const P: u8> $imp<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<P>>;

            #[inline(always)]
            fn $method(self, other: $t) -> Self::Output {
                let coeff = if P == 0 {
                    i128::$method(self.coeff, other as i128)
                } else {
                    i128::$method(self.coeff, mul_pow_ten(other as i128, P))
                }?;
                Some(Decimal { coeff: coeff })
            }
        }

        impl<const P: u8> $imp<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<P>>;

            #[inline(always)]
            fn $method(self, other: Decimal<P>) -> Self::Output {
                let coeff = if P == 0 {
                    i128::$method(self as i128, other.coeff)
                } else {
                    i128::$method(mul_pow_ten(self as i128, P), other.coeff)
                }?;
                Some(Decimal { coeff: coeff })
            }
        }
        )*
    }
}

impl_checked_add_sub_decimal_and_int!(impl CheckedAdd, checked_add);
forward_ref_binop_decimal_int!(impl CheckedAdd, checked_add);

impl_checked_add_sub_decimal_and_int!(impl CheckedSub, checked_sub);
forward_ref_binop_decimal_int!(impl CheckedSub, checked_sub);

#[cfg(test)]
mod checked_add_sub_integer_tests {
    use rust_fixed_point_decimal_core::ten_pow;

    use super::*;

    macro_rules! gen_checked_add_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = <$t>::MAX;
                let r = d.checked_add(i).unwrap();
                assert_eq!(r.precision(), d.precision());
                assert_eq!(r.coeff, i as i128 * ten_pow($p) + $coeff);
                assert_eq!(r.coeff, (&d).checked_add(i).unwrap().coeff);
                assert_eq!(r.coeff, d.checked_add(&i).unwrap().coeff);
                assert_eq!(r.coeff, (&d).checked_add(&i).unwrap().coeff);
                let z = CheckedAdd::checked_add(i, d).unwrap();
                assert_eq!(z.coeff, r.coeff);
                assert_eq!(
                    z.coeff,
                    CheckedAdd::checked_add(&i, d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedAdd::checked_add(i, &d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedAdd::checked_add(&i, &d).unwrap().coeff
                );
                let d = Decimal::<$p>::MAX;
                let i: $t = 1;
                let z = d.checked_add(i);
                assert!(z.is_none());
            }
        };
    }

    gen_checked_add_integer_tests!(test_checked_add_u8, u8, 2, 1);
    gen_checked_add_integer_tests!(test_checked_add_i8, i8, 0, 123);
    gen_checked_add_integer_tests!(test_checked_add_u16, u16, 4, 11);
    gen_checked_add_integer_tests!(test_checked_add_i16, i16, 4, 1234567);
    gen_checked_add_integer_tests!(test_checked_add_u32, u32, 1, 0);
    gen_checked_add_integer_tests!(test_checked_add_i32, i32, 9, 1234);
    gen_checked_add_integer_tests!(test_checked_add_u64, u64, 3, 321);
    gen_checked_add_integer_tests!(
        test_checked_add_i64,
        i64,
        7,
        12345678901234567890
    );

    #[test]
    fn test_checked_add_i128() {
        let d = Decimal::<2>::new_raw(1);
        let i = 12345_i128;
        let r = d.checked_add(i).unwrap();
        assert_eq!(r.coeff, i * 100 + 1);
        assert_eq!(r.coeff, (&d).checked_add(i).unwrap().coeff);
        assert_eq!(r.coeff, d.checked_add(&i).unwrap().coeff);
        assert_eq!(r.coeff, (&d).checked_add(&i).unwrap().coeff);
        let z = CheckedAdd::checked_add(i, d).unwrap();
        assert_eq!(z.coeff, r.coeff);
        assert_eq!(z.coeff, CheckedAdd::checked_add(&i, d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedAdd::checked_add(i, &d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedAdd::checked_add(&i, &d).unwrap().coeff);
    }

    macro_rules! gen_checked_sub_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = <$t>::MAX;
                let r = d.checked_sub(i).unwrap();
                assert_eq!(r.coeff, $coeff - i as i128 * ten_pow($p));
                assert_eq!(r.coeff, (&d).checked_sub(i).unwrap().coeff);
                assert_eq!(r.coeff, d.checked_sub(&i).unwrap().coeff);
                assert_eq!(r.coeff, (&d).checked_sub(&i).unwrap().coeff);
                let z = CheckedSub::checked_sub(i, d).unwrap();
                assert_eq!(z.coeff, i as i128 * ten_pow($p) - $coeff);
                assert_eq!(
                    z.coeff,
                    CheckedSub::checked_sub(&i, d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedSub::checked_sub(i, &d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedSub::checked_sub(&i, &d).unwrap().coeff
                );
                let d = Decimal::<$p>::MIN;
                let i: $t = 1;
                let z = d.checked_sub(i);
                assert!(z.is_none());
            }
        };
    }

    gen_checked_sub_integer_tests!(test_checked_sub_u8, u8, 2, 1);
    gen_checked_sub_integer_tests!(test_checked_sub_i8, i8, 0, 123);
    gen_checked_sub_integer_tests!(test_checked_sub_u16, u16, 4, 11);
    gen_checked_sub_integer_tests!(test_checked_sub_i16, i16, 4, 1234567);
    gen_checked_sub_integer_tests!(test_checked_sub_u32, u32, 1, 0);
    gen_checked_sub_integer_tests!(test_checked_sub_i32, i32, 9, 1234);
    gen_checked_sub_integer_tests!(test_checked_sub_u64, u64, 3, 321);
    gen_checked_sub_integer_tests!(
        test_checked_sub_i64,
        i64,
        7,
        12345678901234567890
    );

    #[test]
    fn test_checked_sub_i128() {
        let d = Decimal::<2>::new_raw(501);
        let i = 12345_i128;
        let r = d.checked_sub(i).unwrap();
        assert_eq!(r.coeff, -i * 100 + 501);
        assert_eq!(r.coeff, (&d).checked_sub(i).unwrap().coeff);
        assert_eq!(r.coeff, d.checked_sub(&i).unwrap().coeff);
        assert_eq!(r.coeff, (&d).checked_sub(&i).unwrap().coeff);
        let z = CheckedSub::checked_sub(i, d).unwrap();
        assert_eq!(z.coeff, i * 100 - 501);
        assert_eq!(z.coeff, CheckedSub::checked_sub(&i, d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedSub::checked_sub(i, &d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedSub::checked_sub(&i, &d).unwrap().coeff);
    }
}
