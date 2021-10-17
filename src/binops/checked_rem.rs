// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::cmp::Ordering;

use num::{One, Zero};
use rust_fixed_point_decimal_core::{checked_mul_pow_ten, mul_pow_ten};

use crate::{
    binops::{checked_add_sub::CheckedSub, const_max_u8},
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

pub trait CheckedRem<Rhs = Self> {
    type Output;
    fn checked_rem(self, rhs: Rhs) -> Self::Output;
}

impl<const P: u8, const Q: u8> CheckedRem<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
    PrecLimitCheck<{ const_max_u8(P, Q) <= MAX_PREC }>: True,
{
    type Output = <Decimal<P> as CheckedSub<Decimal<Q>>>::Output;

    #[inline(always)]
    fn checked_rem(self, other: Decimal<Q>) -> Self::Output {
        if other.eq_zero() {
            return None;
        }
        let rem_coeff = match P.cmp(&Q) {
            Ordering::Equal => self.coeff.checked_rem(other.coeff),
            Ordering::Greater => {
                // TODO: try to reduce shift in case of overflow
                let shifted_coeff = checked_mul_pow_ten(other.coeff, P - Q)?;
                self.coeff.checked_rem(shifted_coeff)
            }
            Ordering::Less => {
                // TODO: try to reduce shift in case of overflow
                let shifted_coeff = checked_mul_pow_ten(self.coeff, Q - P)?;
                shifted_coeff.checked_rem(other.coeff)
            }
        }?;
        Some(Decimal { coeff: rem_coeff })
    }
}

forward_ref_binop!(impl CheckedRem, checked_rem);

#[cfg(test)]
mod checked_rem_decimal_tests {
    use super::*;

    #[test]
    fn test_checked_rem_same_prec() {
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<2>::new_raw(300);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, 102);
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<2>::new_raw(-307);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, 88);
        let x = Decimal::<2>::new_raw(-702);
        let y = Decimal::<2>::new_raw(307);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, -88);
        let x = Decimal::<3>::new_raw(702);
        let y = Decimal::<2>::new_raw(300);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, 702);
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<5>::new_raw(-307);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, 198);
        let x = Decimal::<2>::new_raw(-702);
        let y = Decimal::<4>::new_raw(307);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, -204);
    }

    #[test]
    fn test_checked_rem_by_one() {
        let x = Decimal::<2>::new_raw(702);
        let y = Decimal::<4>::ONE;
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, x.fract().coeff * 100);
        let x = Decimal::<4>::new_raw(70389032);
        let y = Decimal::<2>::ONE;
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coeff, x.fract().coeff);
    }
}

macro_rules! impl_checked_rem_decimal_and_int {
    () => {
        impl_checked_rem_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> CheckedRem<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<P>>;

            fn checked_rem(self, other: $t) -> Self::Output {
                if other.is_zero() {
                    return None;
                }
                if other.is_one() {
                    return Some(self.fract());
                }
                let rem_coeff = if P == 0 {
                    self.coeff.checked_rem(other as i128)
                } else {
                    let shifted_coeff = checked_mul_pow_ten(other as i128, P)?;
                    self.coeff.checked_rem(shifted_coeff)
                }?;
                Some(Decimal { coeff: rem_coeff })
            }
        }

        impl<const P: u8> CheckedRem<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<P>>;

            fn checked_rem(self, other: Decimal<P>) -> Self::Output {
                if other.eq_zero() {
                    return None;
                }
                if other.eq_one() {
                    return Some(Decimal::<P>::ZERO);
                }
                let rem_coeff = if P == 0 {
                    (self as i128).checked_rem(other.coeff)
                } else {
                    let shifted_coeff = checked_mul_pow_ten(self as i128, P)?;
                    shifted_coeff.checked_rem(other.coeff)
                }?;
                Some(Decimal { coeff: rem_coeff })
            }
        }
        )*
    }
}

impl_checked_rem_decimal_and_int!();
forward_ref_binop_decimal_int!(impl CheckedRem, checked_rem);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod checked_rem_integer_tests {
    use num::{One, Zero};

    use super::*;

    macro_rules! gen_checked_rem_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i: $t = 127;
                let c = mul_pow_ten(i as i128, $p);
                let r = d.checked_rem(i).unwrap();
                assert_eq!(r.coeff, $coeff - c * ($coeff / c));
                assert_eq!(r.coeff, (&d).checked_rem(i).unwrap().coeff);
                assert_eq!(r.coeff, d.checked_rem(&i).unwrap().coeff);
                assert_eq!(r.coeff, (&d).checked_rem(&i).unwrap().coeff);
                let z = CheckedRem::checked_rem(i, d).unwrap();
                assert_eq!(z.coeff, c - $coeff * (c / $coeff));
                assert_eq!(
                    z.coeff,
                    CheckedRem::checked_rem(&i, d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedRem::checked_rem(i, &d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedRem::checked_rem(&i, &d).unwrap().coeff
                );
            }
        };
    }

    gen_checked_rem_integer_tests!(test_checked_rem_u8, u8, 2, -1);
    gen_checked_rem_integer_tests!(test_checked_rem_i8, i8, 0, 253);
    gen_checked_rem_integer_tests!(test_checked_rem_u16, u16, 4, 804);
    gen_checked_rem_integer_tests!(test_checked_rem_i16, i16, 4, 390625);
    gen_checked_rem_integer_tests!(test_checked_rem_u32, u32, 1, 1014);
    gen_checked_rem_integer_tests!(test_checked_rem_i32, i32, 9, -1000);
    gen_checked_rem_integer_tests!(test_checked_rem_u64, u64, 3, 206);
    gen_checked_rem_integer_tests!(test_checked_rem_i64, i64, 7, -488281250);
    gen_checked_rem_integer_tests!(
        test_checked_rem_i128,
        i128,
        2,
        1526281250433765
    );

    #[test]
    fn test_checked_rem_decimal_by_int_one() {
        let x = Decimal::<5>::new_raw(17294738475);
        let y = i64::one();
        let z = x.checked_rem(y).unwrap();
        assert_eq!(z.coeff, x.fract().coeff);
        let y = u8::one();
        let z = x.checked_rem(y).unwrap();
        assert_eq!(z.coeff, x.fract().coeff);
    }

    #[test]
    fn test_checked_rem_int_by_decimal_one() {
        let x = 17_i32;
        let y = Decimal::<5>::ONE;
        let z = CheckedRem::checked_rem(x, y).unwrap();
        assert_eq!(z.coeff, 0);
        let x = u64::one();
        let z = CheckedRem::checked_rem(x, y).unwrap();
        assert_eq!(z.coeff, 0);
    }

    #[test]
    fn test_checked_rem_decimal_by_int_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = i32::zero();
        let z = x.checked_rem(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_rem_int_by_decimal_zero() {
        let x = 25_u64;
        let y = Decimal::<3>::ZERO;
        let z = CheckedRem::checked_rem(x, y);
        assert!(z.is_none());
    }
}
