// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::convert::TryFrom;

use num::{traits::float::FloatCore, BigInt, One};
use rust_fixed_point_decimal_core::ten_pow;

use crate::{
    errors::DecimalError,
    prec_constraints::{PrecLimitCheck, True},
    rounding::div_i128_rounded,
    Decimal,
};

macro_rules! impl_from_float {
    () => {
        impl_from_float!(f32, f64);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> TryFrom<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
        {
            type Error = DecimalError;

            fn try_from(f: $t) -> Result<Self, Self::Error> {
                if f.is_infinite() {
                    return Err(DecimalError::InfiniteValue);
                }
                if f.is_nan() {
                    return Err(DecimalError::NotANumber);
                }
                let (mantissa, exponent, sign) = f.integer_decode();
                if exponent < -126 {
                    Ok(Decimal::ZERO)
                }
                else if exponent < 0 {
                    let numer = i128::from(sign)
                        * i128::from(mantissa)
                        * ten_pow(P);
                    let denom = i128::one() << ((-exponent) as usize);
                    let coeff = div_i128_rounded(numer, denom, None);
                    Ok(Decimal { coeff })
                } else {
                    let mut numer = BigInt::from(mantissa);
                    numer <<= exponent as usize;
                    numer *= BigInt::from(sign) * BigInt::from(ten_pow(P));
                    match i128::try_from(numer) {
                        Err(_) => Err(DecimalError::MaxValueExceeded),
                        Ok(coeff) => Ok(Decimal { coeff }),
                    }
                }
            }
        }
        )*
    }
}

impl_from_float!();

#[cfg(test)]
mod tests {
    use num::traits::float::FloatCore;

    use super::*;
    use crate::MAX_PREC;

    fn check_from_float<const P: u8, T>(test_data: &[(T, i128)])
    where
        PrecLimitCheck<{ P <= MAX_PREC }>: True,
        T: FloatCore,
        Decimal<P>: TryFrom<T>,
    {
        for (val, coeff) in test_data {
            match Decimal::<P>::try_from(*val) {
                Err(_) => panic!("Mismatched test data!"),
                Ok(d) => {
                    assert_eq!(d.coeff, *coeff);
                    assert_eq!(d.precision(), P);
                }
            }
        }
    }

    #[test]
    fn test_decimal0_from_f32() {
        let test_data = [
            (i128::MIN as f32, i128::MIN),
            (-289.04, -289),
            (-2.5, -2),
            (0.0, 0),
            (5.2, 5),
            ((i128::MAX / 2) as f32, i128::MAX / 2 + 1),
        ];
        check_from_float::<0, f32>(&test_data)
    }

    #[test]
    fn test_decimal4_from_f32() {
        let test_data = [
            (-289.5, -2895000),
            (-0.5, -5000),
            (0.0, 0),
            (37.0005003, 370005),
        ];
        check_from_float::<4, f32>(&test_data)
    }

    #[test]
    fn test_decimal0_from_f64() {
        let test_data = [
            (i128::MIN as f64, i128::MIN),
            (-289.4, -289),
            (-2.5, -2),
            (0.0, 0),
            (5.2, 5),
            ((i128::MAX / 2) as f64, i128::MAX / 2 + 1),
        ];
        check_from_float::<0, f64>(&test_data)
    }

    #[test]
    fn test_decimal9_from_f64() {
        let test_data = [
            (-28900.000000005, -28900000000005),
            (-5e-7, -500),
            (1.004e-127, 0),
            (0.0, 0),
            (1.0005, 1000500000),
            (37.0005000033, 37000500003),
        ];
        check_from_float::<9, f64>(&test_data)
    }

    #[test]
    fn test_fail_on_f32_infinite_value() {
        for f in [f32::infinity(), f32::neg_infinity()] {
            let res = Decimal::<2>::try_from(f);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, DecimalError::InfiniteValue);
        }
    }

    #[test]
    fn test_fail_on_f64_infinite_value() {
        for f in [f64::infinity(), f64::neg_infinity()] {
            let res = Decimal::<2>::try_from(f);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, DecimalError::InfiniteValue);
        }
    }

    #[test]
    fn test_fail_on_f32_nan() {
        let f = f32::nan();
        let res = Decimal::<2>::try_from(f);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, DecimalError::NotANumber);
    }

    #[test]
    fn test_fail_on_f64_nan() {
        let f = f64::nan();
        let res = Decimal::<7>::try_from(f);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, DecimalError::NotANumber);
    }
}
