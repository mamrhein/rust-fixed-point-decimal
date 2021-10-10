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
    ops::{Rem, Sub},
};

use num::Zero;
use rust_fixed_point_decimal_core::mul_pow_ten;

use crate::{
    binops::const_max_u8,
    prec_constraints::{PrecLimitCheck, True},
    Decimal, DecimalError, MAX_PREC,
};

impl<const P: u8, const Q: u8> Rem<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
    PrecLimitCheck<{ const_max_u8(P, Q) <= MAX_PREC }>: True,
{
    type Output = <Decimal<P> as Sub<Decimal<Q>>>::Output;

    #[inline(always)]
    fn rem(self, other: Decimal<Q>) -> Self::Output {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        match P.cmp(&Q) {
            Ordering::Equal => Self::Output {
                coeff: self.coeff % other.coeff,
            },
            Ordering::Greater => Self::Output {
                coeff: self.coeff % mul_pow_ten(other.coeff, P - Q),
            },
            Ordering::Less => Self::Output {
                coeff: mul_pow_ten(self.coeff, Q - P) % other.coeff,
            },
        }
    }
}

forward_ref_binop!(impl Rem, rem);

#[cfg(test)]
mod rem_decimal_tests {
    use super::*;

    #[test]
    fn test_rem_same_prec() {
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<2>::new_raw(300);
        let r = x % y;
        assert_eq!(r.coeff, 102);
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<2>::new_raw(-307);
        let r = x % y;
        assert_eq!(r.coeff, 88);
        let x = Decimal::<2>::new_raw(-702);
        let y = Decimal::<2>::new_raw(307);
        let r = x % y;
        assert_eq!(r.coeff, -88);
    }

    #[test]
    fn test_rem_diff_prec() {
        let x = Decimal::<3>::new_raw(702);
        let y = Decimal::<2>::new_raw(300);
        let r = x % y;
        assert_eq!(r.coeff, 702);
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<5>::new_raw(-307);
        let r = x % y;
        assert_eq!(r.coeff, 198);
        let x = Decimal::<2>::new_raw(-702);
        let y = Decimal::<4>::new_raw(307);
        let r = x % y;
        assert_eq!(r.coeff, -204);
    }

    #[test]
    fn test_rem_by_one() {
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<4>::ONE;
        let r = x % y;
        assert_eq!(r.coeff, x.fract().coeff * 100);
        let x = Decimal::<4>::new_raw(70389032);
        let y = Decimal::<2>::ONE;
        let r = x % y;
        assert_eq!(r.coeff, x.fract().coeff);
    }
}

macro_rules! impl_rem_decimal_and_int {
    () => {
        impl_rem_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> Rem<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<P>;

            fn rem(self, other: $t) -> Self::Output {
                if other.is_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if P == 0 {
                    Self::Output { coeff: self.coeff % other as i128 }
                } else {
                    Self::Output {
                        coeff: self.coeff % mul_pow_ten(other as i128, P)
                    }
                }
            }
        }

        impl<const P: u8> Rem<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<P>;

            fn rem(self, other: Decimal<P>) -> Self::Output {
                if other.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if P == 0 {
                    Self::Output { coeff: self as i128 % other.coeff }
                } else {
                    Self::Output {
                        coeff: mul_pow_ten(self as i128, P) % other.coeff
                    }
                }
            }
        }
        )*
    }
}

impl_rem_decimal_and_int!();
forward_ref_binop_decimal_int!(impl Rem, rem);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod rem_integer_tests {
    use num::{One, Zero};

    use super::*;

    macro_rules! gen_rem_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i: $t = 127;
                let c = mul_pow_ten(i as i128, $p);
                let r = d % i;
                assert_eq!(r.precision(), $p);
                assert_eq!(r.coeff, $coeff - c * ($coeff / c));
                assert_eq!(r.coeff, (&d % i).coeff);
                assert_eq!(r.coeff, (d % &i).coeff);
                assert_eq!(r.coeff, (&d % &i).coeff);
                let z = i % d;
                assert_eq!(z.precision(), $p);
                assert_eq!(z.coeff, c - $coeff * (c / $coeff));
                assert_eq!(z.coeff, (&i % d).coeff);
                assert_eq!(z.coeff, (i % &d).coeff);
                assert_eq!(z.coeff, (&i % &d).coeff);
            }
        };
    }

    gen_rem_integer_tests!(test_rem_u8, u8, 2, -1);
    gen_rem_integer_tests!(test_rem_i8, i8, 0, 253);
    gen_rem_integer_tests!(test_rem_u16, u16, 4, 804);
    gen_rem_integer_tests!(test_rem_i16, i16, 4, 390625);
    gen_rem_integer_tests!(test_rem_u32, u32, 1, 1014);
    gen_rem_integer_tests!(test_rem_i32, i32, 9, -1000);
    gen_rem_integer_tests!(test_rem_u64, u64, 3, 206);
    gen_rem_integer_tests!(test_rem_i64, i64, 7, -488281250);
    gen_rem_integer_tests!(test_rem_i128, i128, 2, 1526281250433765);

    #[test]
    fn test_rem_decimal_by_int_one() {
        let x = Decimal::<5>::new_raw(17294738475);
        let y = i64::one();
        let z = x % y;
        assert_eq!(z.coeff, x.fract().coeff);
        let y = u8::one();
        let z = x % y;
        assert_eq!(z.coeff, x.fract().coeff);
    }

    #[test]
    fn test_rem_int_by_decimal_one() {
        let x = 17_i32;
        let y = Decimal::<5>::ONE;
        let z = x % y;
        assert_eq!(z.coeff, 0);
        let x = u64::one();
        let z = x % y;
        assert_eq!(z.coeff, 0);
    }

    #[test]
    #[should_panic]
    fn test_rem_decimal_by_int_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = i32::zero();
        let _z = x % y;
    }

    #[test]
    #[should_panic]
    fn test_rem_int_by_decimal_zero() {
        let x = 25;
        let y = Decimal::<3>::ZERO;
        let _z = x % y;
    }
}
