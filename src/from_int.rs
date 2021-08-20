// ----------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ----------------------------------------------------------------------------
// $Source$
// $Revision$

use std::convert::TryFrom;

use crate::{
    errors::DecimalError,
    powers_of_ten::{checked_mul_pow_ten, ten_pow},
    Decimal, PrecLimitCheck, True,
};

macro_rules! impl_from_int {
    () => {
        impl_from_int!(u8, i8, u16, i16, u32, i32, u64, i64);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> From<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
        {
            #[inline]
            fn from(i: $t) -> Self
            {
                Decimal { coeff: i as i128 * ten_pow(P) as i128 }
            }
        }
        )*
    }
}

impl_from_int!();

impl<const P: u8> TryFrom<i128> for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    type Error = DecimalError;

    #[inline]
    fn try_from(i: i128) -> Result<Self, Self::Error> {
        match checked_mul_pow_ten(i, P) {
            None => Err(DecimalError::MaxValueExceeded),
            Some(coeff) => Ok(Decimal { coeff }),
        }
    }
}

impl<const P: u8> TryFrom<u128> for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    type Error = DecimalError;

    #[inline]
    fn try_from(i: u128) -> Result<Self, Self::Error> {
        match i128::try_from(i) {
            Err(_) => Err(DecimalError::MaxValueExceeded),
            Ok(i) => Self::try_from(i),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;

    use super::*;

    fn check_from_int<const P: u8, T>(numbers: &[T])
    where
        PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
        T: Into<i128> + Copy,
        Decimal<P>: From<T>,
    {
        for n in numbers {
            let d = Decimal::<P>::from(*n);
            assert_eq!(d.coeff / ten_pow(P), (*n).into());
            assert_eq!(d.precision(), P);
        }
    }

    #[test]
    fn test_from_u8() {
        let numbers: [u8; 4] = [0, 1, 28, 255];
        check_from_int::<2, u8>(&numbers);
    }

    #[test]
    fn test_from_i8() {
        let numbers: [i8; 7] = [-128, -38, -1, 0, 1, 28, 127];
        check_from_int::<0, i8>(&numbers);
    }

    #[test]
    fn test_from_u64() {
        let numbers: [u64; 4] = [0, 1, 2128255, u64::MAX];
        check_from_int::<9, u64>(&numbers);
    }

    #[test]
    fn test_from_i64() {
        let numbers: [i64; 4] = [0, -1, 2128255, i64::MIN];
        check_from_int::<3, i64>(&numbers);
    }

    fn check_try_from_int_ok<const P: u8, T>(numbers: &[T])
    where
        PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
        T: TryInto<i128> + Copy,
        Decimal<P>: TryFrom<T>,
    {
        for n in numbers {
            match Decimal::<P>::try_from(*n) {
                Err(_) => panic!("Mismatched test value!"),
                Ok(d) => match (*n).try_into() {
                    Err(_) => panic!("Should never happen!"),
                    Ok(i) => {
                        assert_eq!(d.coeff / ten_pow(P), i);
                        assert_eq!(d.precision(), P);
                    }
                },
            }
        }
    }

    #[test]
    fn test_from_u128_ok() {
        let numbers: [u128; 4] =
            [0, 1, 2128255, 170141183460469231731687303715884105727u128];
        check_try_from_int_ok::<0, u128>(&numbers);
    }

    #[test]
    fn test_from_i128_ok() {
        let numbers: [i128; 7] = [
            -170141183460469231731687303715884105728,
            -3830009274,
            -1,
            0,
            1,
            2829773566410082,
            170141183460469231731687303715884105727,
        ];
        check_try_from_int_ok::<0, i128>(&numbers);
    }

    #[test]
    fn test_from_i128_err() {
        let numbers: [i128; 2] = [
            -170141183460469231731687303715884105728,
            170141183460469231731687303715884105727,
        ];
        for i in numbers {
            let res = Decimal::<1>::try_from(i);
            assert_eq!(res.unwrap_err(), DecimalError::MaxValueExceeded);
        }
    }

    #[test]
    fn test_from_u128_err() {
        let i = 170141183460469231731687303715884105728u128;
        let res = Decimal::<0>::try_from(i);
        assert_eq!(res.unwrap_err(), DecimalError::MaxValueExceeded);
        let i = 17014118346046923173168730371588410572u128;
        let res = Decimal::<3>::try_from(i);
        assert_eq!(res.unwrap_err(), DecimalError::MaxValueExceeded);
    }

    #[test]
    fn test_from() {
        let di32 = Decimal::<3>::from(-358i32);
        assert_eq!(di32.coeff, -358000i128);
        let i = 38i64.pow(12);
        let di64 = Decimal::<0>::from(i);
        assert_eq!(di64.coeff, i as i128);
    }

    #[test]
    fn test_into() {
        let du8: Decimal<9> = 38u8.into();
        assert_eq!(du8.coeff, 38000000000);
        let i = -1234567890123456789i64;
        let di64: Decimal<0> = i.into();
        assert_eq!(di64.coeff, i as i128);
    }
}
