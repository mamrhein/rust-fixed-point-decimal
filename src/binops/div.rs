// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::{Div, DivAssign};

use num::{integer::div_mod_floor, One, Zero};
use rust_fixed_point_decimal_core::mul_pow_ten;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal, DecimalError, MAX_PREC,
};

impl<const P: u8, const Q: u8> Div<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
{
    type Output = Decimal<9>;

    fn div(self, other: Decimal<Q>) -> Self::Output {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        if other.eq_one() {
            return Self::Output {
                coeff: mul_pow_ten(self.coeff, MAX_PREC - P),
            };
        }
        let r = MAX_PREC + Q - P;
        // TODO: try to avoid overflowing shifted coeff
        let (quot, rem) =
            div_mod_floor(mul_pow_ten(self.coeff, r), other.coeff);
        if rem != 0 {
            panic!("{}", DecimalError::PrecLimitExceeded);
        }
        Self::Output { coeff: quot }
    }
}

forward_ref_binop!(impl Div, div);

#[cfg(test)]
mod div_decimal_tests {
    use super::*;

    #[test]
    fn test_div() {
        let x = Decimal::<0>::new_raw(17);
        let y = Decimal::<2>::new_raw(-200);
        let z = x / y;
        assert_eq!(z.coeff, -8500000000);
        let x = Decimal::<8>::new_raw(17);
        let y = Decimal::<0>::new_raw(2);
        let z = x / y;
        assert_eq!(z.coeff, 85);
        let x = Decimal::<2>::new_raw(12345678901234567890);
        let y = Decimal::<6>::new_raw(244140625);
        let z = x / y;
        assert_eq!(z.coeff, 505679007794567900774400);
    }

    #[test]
    fn test_div_by_one() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ONE;
        let z = x / y;
        assert_eq!(z.coeff, 170000);
        let y = Decimal::<9>::ONE;
        let z = x / y;
        assert_eq!(z.coeff, 170000);
    }

    #[test]
    #[should_panic]
    fn test_div_by_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ZERO;
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_prec_limit_exceeded() {
        let x = Decimal::<9>::new_raw(17);
        let y = Decimal::<0>::new_raw(2);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_overflow() {
        let x = Decimal::<0>::new_raw(mul_pow_ten(17, 20));
        let y = Decimal::<9>::new_raw(2);
        let _z = x / y;
    }

    #[test]
    fn test_div_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<1>::new_raw(12345);
        let z = x / y;
        assert_eq!(z.coeff, (&x / y).coeff);
        assert_eq!(z.coeff, (x / &y).coeff);
        assert_eq!(z.coeff, (&x / &y).coeff);
    }
}

macro_rules! impl_div_decimal_and_int {
    () => {
        impl_div_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> Div<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<9>;

            fn div(self, other: $t) -> Self::Output {
                if other.is_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if other.is_one() {
                    return Self::Output {
                        coeff: mul_pow_ten(self.coeff, MAX_PREC - P),
                    };
                }
                let r = MAX_PREC - P;
                let (quot, rem) =
                    div_mod_floor(mul_pow_ten(self.coeff, r), other as i128);
                if rem != 0 {
                    panic!("{}", DecimalError::PrecLimitExceeded);
                }
                Self::Output { coeff: quot }
            }
        }

        impl<const P: u8> Div<Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            type Output = Decimal<9>;

            fn div(self, other: Decimal<P>) -> Self::Output {
                if other.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if other.eq_one() {
                    return Self::Output {
                        coeff: mul_pow_ten(self as i128, MAX_PREC),
                    };
                }
                let r = MAX_PREC + P;
                let (quot, rem) =
                    div_mod_floor(mul_pow_ten(self as i128, r), other.coeff);
                if rem != 0 {
                    panic!("{}", DecimalError::PrecLimitExceeded);
                }
                Self::Output { coeff: quot }
            }
        }
        )*
    }
}

impl_div_decimal_and_int!();
forward_ref_binop_decimal_int!(impl Div, div);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod div_integer_tests {
    use num::{One, Zero};
    use rust_fixed_point_decimal_core::ten_pow;

    use super::*;

    macro_rules! gen_div_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i: $t = 10;
                let r = d / i;
                assert_eq!(r.precision(), MAX_PREC);
                assert_eq!(
                    r.coeff,
                    $coeff * ten_pow(MAX_PREC - $p) / i as i128
                );
                assert_eq!(r.coeff, (&d / i).coeff);
                assert_eq!(r.coeff, (d / &i).coeff);
                assert_eq!(r.coeff, (&d / &i).coeff);
                let z = i / d;
                assert_eq!(z.precision(), MAX_PREC);
                assert_eq!(
                    z.coeff,
                    i as i128 * ten_pow(MAX_PREC + $p) / $coeff
                );
                assert_eq!(z.coeff, (&i / d).coeff);
                assert_eq!(z.coeff, (i / &d).coeff);
                assert_eq!(z.coeff, (&i / &d).coeff);
            }
        };
    }

    gen_div_integer_tests!(test_div_u8, u8, 2, -1);
    gen_div_integer_tests!(test_div_i8, i8, 0, 250);
    gen_div_integer_tests!(test_div_u16, u16, 4, 80);
    gen_div_integer_tests!(test_div_i16, i16, 4, 390625);
    gen_div_integer_tests!(test_div_u32, u32, 1, 10);
    gen_div_integer_tests!(test_div_i32, i32, 9, -1000);
    gen_div_integer_tests!(test_div_u64, u64, 3, 20);
    gen_div_integer_tests!(test_div_i64, i64, 7, -488281250);

    #[test]
    fn test_div_i128() {
        let coeff = 2002_i128;
        let d = Decimal::<4>::new_raw(coeff);
        let i = 5005_i128;
        let r = d / i;
        assert_eq!(r.precision(), MAX_PREC);
        assert_eq!(r.coeff, coeff * 100000 / i);
        assert_eq!(r.coeff, (&d / i).coeff);
        assert_eq!(r.coeff, (d / &i).coeff);
        assert_eq!(r.coeff, (&d / &i).coeff);
        let z = i / d;
        assert_eq!(z.precision(), MAX_PREC);
        assert_eq!(z.coeff, i * ten_pow(13) / coeff);
        assert_eq!(z.coeff, (&i / d).coeff);
        assert_eq!(z.coeff, (i / &d).coeff);
        assert_eq!(z.coeff, (&i / &d).coeff);
    }

    #[test]
    fn test_div_decimal_by_int_one() {
        let x = Decimal::<5>::new_raw(17);
        let y = i64::one();
        let z = x / y;
        assert_eq!(z.coeff, 170000);
        let y = u8::one();
        let z = x / y;
        assert_eq!(z.coeff, 170000);
    }

    #[test]
    fn test_div_int_by_decimal_one() {
        let x = 17;
        let y = Decimal::<5>::ONE;
        let z: Decimal<9> = x / y;
        assert_eq!(z.coeff, 17000000000);
        let x = u64::one();
        let z = x / y;
        assert_eq!(z.coeff, 1000000000);
    }

    #[test]
    #[should_panic]
    fn test_div_decimal_by_int_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = i32::zero();
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_int_by_decimal_zero() {
        let x = 25;
        let y = Decimal::<3>::ZERO;
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_decimal_by_int_prec_limit_exceeded() {
        let x = Decimal::<2>::new_raw(17);
        let y = 3;
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_int_by_decimal_prec_limit_exceeded() {
        let x = 3;
        let y = Decimal::<2>::new_raw(17);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_int_by_decimal_overflow() {
        let x = mul_pow_ten(17, 20);
        let y = Decimal::<9>::new_raw(2);
        let _z = x / y;
    }
}

forward_op_assign!(impl DivAssign, div_assign, Div, div);

#[cfg(test)]
mod div_assign_tests {
    use super::*;

    #[test]
    fn test_div_assign_decimal() {
        let mut x = Decimal::<9>::new_raw(1234567890);
        x /= Decimal::<3>::new_raw(5000);
        assert_eq!(x.coeff, 123456789 * 2);
    }

    #[test]
    fn test_div_assign_int() {
        let mut x = Decimal::<9>::new_raw(1234567890);
        x /= -10_i64;
        assert_eq!(x.coeff, -123456789);
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_int_zero() {
        let mut x = Decimal::<9>::new_raw(17);
        let y = i32::zero();
        x /= y;
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_decimal_zero() {
        let mut x = Decimal::<9>::new_raw(25);
        let y = Decimal::<3>::ZERO;
        x /= y;
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_int_prec_limit_exceeded() {
        let mut x = Decimal::<9>::new_raw(17);
        let y = 3;
        x /= y;
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_decimal_prec_limit_exceeded() {
        let mut x = Decimal::<9>::new_raw(17);
        let y = Decimal::<4>::new_raw(50000);
        x /= y;
    }
}
