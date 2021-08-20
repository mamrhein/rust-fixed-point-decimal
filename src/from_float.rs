// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::convert::TryFrom;

use num::{
    integer::div_mod_floor, traits::float::FloatCore, BigInt, One, Zero,
};

use crate::{
    errors::DecimalError,
    powers_of_ten::ten_pow,
    prec_constraints::{PrecLimitCheck, True},
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
                let (mantissa, exponent, sign) = f.integer_decode();
                if exponent < 0 {
                    let numer = BigInt::from(sign)
                        * BigInt::from(mantissa)
                        * BigInt::from(ten_pow(P));
                    let denom = BigInt::one() << ((-exponent) as usize);
                    let (quot, rem) = div_mod_floor(numer, denom);
                    if rem != BigInt::zero() {
                        return Err(DecimalError::PrecLimitExceeded);
                    }
                    match i128::try_from(quot) {
                        Err(_) => Err(DecimalError::MaxValueExceeded),
                        Ok(coeff) => Ok(Decimal { coeff }),
                    }
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
    use num::{traits::float::FloatCore, BigInt, BigRational};

    use super::*;

    fn check_from_float<const P: u8, T>(numbers: &[T])
    where
        PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
        T: FloatCore,
        Decimal<P>: TryFrom<T>,
    {
        for f in numbers {
            let rbig = BigRational::from_float(*f).unwrap();
            let (num, den) = (rbig.numer(), rbig.denom());
            let coeff = if den == &BigInt::one() {
                num.clone() * ten_pow(P)
            } else {
                num * ten_pow(P) / den
            };
            match Decimal::<P>::try_from(*f) {
                Err(_) => panic!("Mismatched test data!"),
                Ok(d) => {
                    assert_eq!(BigInt::from(d.coeff), coeff);
                    assert_eq!(d.precision(), P);
                }
            }
        }
    }

    #[test]
    fn test_decimal0_from_f32() {
        let numbers = [
            i128::MIN as f32,
            -289.0,
            -2.,
            0.0,
            5.,
            (i128::MAX / 2) as f32,
        ];
        check_from_float::<0, f32>(&numbers)
    }

    #[test]
    fn test_decimal4_from_f32() {
        let numbers = [-289.5, -0.5, 0.0, 37.5];
        check_from_float::<4, f32>(&numbers)
    }

    // #[test]
    // fn ratio_from_f64() {
    //     let numbers = [
    //         i128::MIN as f64,
    //         -289.5,
    //         -0.2,
    //         0.0,
    //         1.005,
    //         (i128::MAX / 2) as f64,
    //     ];
    //     check_from_float(&numbers)
    // }
}
