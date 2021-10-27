// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use num::integer::div_mod_floor;
use rust_fixed_point_decimal_core::{checked_mul_pow_ten, ten_pow};

use crate::{errors::DecimalError, Decimal, PrecLimitCheck, True, MAX_PREC};

// Can't implement trait TryFrom here, because it conflicts with crate `core`:
// impl<T, U> std::convert::TryFrom<U> for T where U: Into<T>
// TODO: check again when feature 'specialization' lands
// TODO: make impl pub
// TODO: write doc comment
impl<const P: u8> Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    #[inline]
    fn try_from<const Q: u8>(dec: Decimal<Q>) -> Result<Self, DecimalError>
    where
        PrecLimitCheck<{ Q <= MAX_PREC }>: True,
    {
        if Q == P {
            Ok(Self::new_raw(dec.coeff))
        } else if Q < P {
            match checked_mul_pow_ten(dec.coeff, P - Q) {
                None => Err(DecimalError::MaxValueExceeded),
                Some(coeff) => Ok(Self::new_raw(coeff)),
            }
        } else {
            let (quot, rem) = div_mod_floor(dec.coeff, ten_pow(Q - P));
            if rem != 0 {
                Err(DecimalError::PrecLimitExceeded)
            } else {
                Ok(Self::new_raw(quot))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_try_from_eq_prec() {
        let x = Decimal::<6>::new_raw(1234567890);
        let y = Decimal::<6>::try_from(x).unwrap();
        assert_eq!(x.coeff, y.coeff);
    }

    #[test]
    fn test_try_from_lesser_prec() {
        let x = Decimal::<6>::new_raw(1234567890);
        let y = Decimal::<9>::try_from(x).unwrap();
        assert_eq!(y.coeff / x.coeff, 1000);
    }

    #[test]
    fn test_try_from_lesser_prec_fails() {
        let x = Decimal::<2>::new_raw(i128::MAX / 10 + 1);
        let res = Decimal::<3>::try_from(x);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, DecimalError::MaxValueExceeded);
    }

    #[test]
    fn test_try_from_greater_prec() {
        let x = Decimal::<3>::new_raw(1234567890);
        let y = Decimal::<2>::try_from(x).unwrap();
        assert_eq!(x.coeff / y.coeff, 10);
    }

    #[test]
    fn test_try_from_greater_prec_fails() {
        let x = Decimal::<5>::new_raw(1234567890);
        let res = Decimal::<3>::try_from(x);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, DecimalError::PrecLimitExceeded);
    }
}
