// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use num::{integer::div_mod_floor, One, Zero};
use rust_fixed_point_decimal_core::checked_mul_pow_ten;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

pub trait CheckedDiv<Rhs = Self> {
    type Output;
    fn checked_div(self, rhs: Rhs) -> Self::Output;
}

impl<const P: u8, const Q: u8> CheckedDiv<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
{
    type Output = Option<Decimal<9>>;

    fn checked_div(self, other: Decimal<Q>) -> Self::Output {
        if other.eq_zero() {
            return None;
        }
        if other.eq_one() {
            let shifted_coeff = checked_mul_pow_ten(self.coeff, MAX_PREC - P)?;
            return Some(Decimal::<9> {
                coeff: shifted_coeff,
            });
        }
        let r = MAX_PREC + Q - P;
        // TODO: try to reduce shift in case of overflow
        let shifted_coeff = checked_mul_pow_ten(self.coeff, r)?;
        let (quot, rem) = div_mod_floor(shifted_coeff, other.coeff);
        if rem != 0 {
            None
        } else {
            Some(Decimal::<9> { coeff: quot })
        }
    }
}

forward_ref_binop!(impl CheckedDiv, checked_div);

#[cfg(test)]
mod checked_div_decimal_tests {
    use rust_fixed_point_decimal_core::mul_pow_ten;

    use super::*;

    #[test]
    fn test_checked_div() {
        let x = Decimal::<0>::new_raw(17);
        let y = Decimal::<2>::new_raw(-200);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, -8500000000);
        let x = Decimal::<8>::new_raw(17);
        let y = Decimal::<0>::new_raw(2);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, 85);
        let x = Decimal::<2>::new_raw(12345678901234567890);
        let y = Decimal::<6>::new_raw(244140625);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, 505679007794567900774400);
    }

    #[test]
    fn test_checked_div_by_one() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ONE;
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, 170000);
        let y = Decimal::<9>::ONE;
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, 170000);
    }

    #[test]
    fn test_checked_div_by_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ZERO;
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_prec_limit_exceeded() {
        let x = Decimal::<9>::new_raw(17);
        let y = Decimal::<0>::new_raw(2);
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_overflow() {
        let x = Decimal::<0>::new_raw(mul_pow_ten(17, 20));
        let y = Decimal::<9>::new_raw(2);
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, (&x).checked_div(y).unwrap().coeff);
        assert_eq!(z.coeff, x.checked_div(&y).unwrap().coeff);
        assert_eq!(z.coeff, (&x).checked_div(&y).unwrap().coeff);
    }
}

macro_rules! impl_div_decimal_and_int {
    () => {
        impl_div_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> CheckedDiv<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<9>>;

            fn checked_div(self, other: $t) -> Self::Output {
                if other.is_zero() {
                    return None;
                }
                if other.is_one() {
                    let shifted_coeff = checked_mul_pow_ten(self.coeff, MAX_PREC - P)?;
                    return Some(Decimal::<9> { coeff: shifted_coeff });
                }
                let r = MAX_PREC - P;
                // TODO: try to reduce shift in case of overflow
                let shifted_coeff = checked_mul_pow_ten(self.coeff, r)?;
                let (quot, rem) = div_mod_floor(shifted_coeff, other as i128);
                if rem != 0 {
                    None
                } else {
                    Some(Decimal::<9> { coeff: quot })
                }
            }
        }

        impl<const P: u8> CheckedDiv<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Option<Decimal<9>>;

            fn checked_div(self, other: Decimal<P>) -> Self::Output {
                if other.eq_zero() {
                    return None;
                }
                if other.eq_one() {
                    let shifted_int = checked_mul_pow_ten(self as i128, MAX_PREC)?;
                    return Some(Decimal::<9> {coeff: shifted_int });
                }
                let r = MAX_PREC + P;
                // TODO: try to reduce shift in case of overflow
                let shifted_int = checked_mul_pow_ten(self as i128, r)?;
                let (quot, rem) = div_mod_floor(shifted_int, other.coeff);
                if rem != 0 {
                    None
                } else {
                    Some(Decimal::<9> { coeff: quot })
                }
            }
        }
        )*
    }
}

impl_div_decimal_and_int!();
forward_ref_binop_decimal_int!(impl CheckedDiv, checked_div);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod checked_div_integer_tests {
    use num::{One, Zero};
    use rust_fixed_point_decimal_core::{mul_pow_ten, ten_pow};

    use super::*;

    macro_rules! gen_checked_div_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i: $t = 10;
                let r = d.checked_div(i).unwrap();
                assert_eq!(r.precision(), MAX_PREC);
                assert_eq!(
                    r.coeff,
                    $coeff * ten_pow(MAX_PREC - $p) / i as i128
                );
                assert_eq!(r.coeff, (&d).checked_div(i).unwrap().coeff);
                assert_eq!(r.coeff, d.checked_div(&i).unwrap().coeff);
                assert_eq!(r.coeff, (&d).checked_div(&i).unwrap().coeff);
                let z = CheckedDiv::checked_div(i, d).unwrap();
                assert_eq!(z.precision(), MAX_PREC);
                assert_eq!(
                    z.coeff,
                    i as i128 * ten_pow(MAX_PREC + $p) / $coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedDiv::checked_div(&i, d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedDiv::checked_div(i, &d).unwrap().coeff
                );
                assert_eq!(
                    z.coeff,
                    CheckedDiv::checked_div(&i, &d).unwrap().coeff
                );
            }
        };
    }

    gen_checked_div_integer_tests!(test_checked_div_u8, u8, 2, -1);
    gen_checked_div_integer_tests!(test_checked_div_i8, i8, 0, 250);
    gen_checked_div_integer_tests!(test_checked_div_u16, u16, 4, 80);
    gen_checked_div_integer_tests!(test_checked_div_i16, i16, 4, 390625);
    gen_checked_div_integer_tests!(test_checked_div_u32, u32, 1, 10);
    gen_checked_div_integer_tests!(test_checked_div_i32, i32, 9, -1000);
    gen_checked_div_integer_tests!(test_checked_div_u64, u64, 3, 20);
    gen_checked_div_integer_tests!(test_checked_div_i64, i64, 7, -488281250);

    #[test]
    fn test_checked_div_i128() {
        let coeff = 2002_i128;
        let d = Decimal::<4>::new_raw(coeff);
        let i = 5005_i128;
        let r = d.checked_div(i).unwrap();
        assert_eq!(r.coeff, coeff * 100000 / i);
        assert_eq!(r.coeff, (&d).checked_div(i).unwrap().coeff);
        assert_eq!(r.coeff, d.checked_div(&i).unwrap().coeff);
        assert_eq!(r.coeff, (&d).checked_div(&i).unwrap().coeff);
        let z = CheckedDiv::checked_div(i, d).unwrap();
        assert_eq!(z.coeff, i * ten_pow(13) / coeff);
        assert_eq!(z.coeff, CheckedDiv::checked_div(&i, d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedDiv::checked_div(i, &d).unwrap().coeff);
        assert_eq!(z.coeff, CheckedDiv::checked_div(&i, &d).unwrap().coeff);
    }

    #[test]
    fn test_checked_div_decimal_by_int_one() {
        let x = Decimal::<5>::new_raw(17);
        let y = i64::one();
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, 170000);
        let y = u8::one();
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coeff, 170000);
    }

    #[test]
    fn test_checked_div_int_by_decimal_one() {
        let x = 17_i32;
        let y = Decimal::<5>::ONE;
        let z = CheckedDiv::checked_div(x, y).unwrap();
        assert_eq!(z.coeff, 17000000000);
        let x = u64::one();
        let z = CheckedDiv::checked_div(x, y).unwrap();
        assert_eq!(z.coeff, 1000000000);
    }

    #[test]
    fn test_checked_div_decimal_by_int_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = i32::zero();
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_int_by_decimal_zero() {
        let x = 25_i64;
        let y = Decimal::<3>::ZERO;
        let z = CheckedDiv::checked_div(x, y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_decimal_by_int_prec_limit_exceeded() {
        let x = Decimal::<2>::new_raw(17);
        let y = 3_u8;
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_int_by_decimal_prec_limit_exceeded() {
        let x = 3_i8;
        let y = Decimal::<2>::new_raw(17);
        let z = CheckedDiv::checked_div(x, y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_int_by_decimal_overflow() {
        let x = mul_pow_ten(17, 20);
        let y = Decimal::<9>::new_raw(2);
        let z = CheckedDiv::checked_div(x, y);
        assert!(z.is_none());
    }
}
