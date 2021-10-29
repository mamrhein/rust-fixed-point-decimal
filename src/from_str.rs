// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{cmp::Ordering, convert::TryFrom, str::FromStr};

use rust_fixed_point_decimal_core::{checked_mul_pow_ten, dec_repr_from_str};

use crate::{Decimal, ParseDecimalError, PrecLimitCheck, True, MAX_PREC};

impl<const P: u8> FromStr for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    type Err = ParseDecimalError;

    /// Convert a number literal into a `Decimal<P>`.
    ///
    /// The literal must be in the form
    ///
    /// `[+|-]<int>[.<frac>][<e|E>[+|-]<exp>]`
    ///
    /// or
    ///
    /// `[+|-].<frac>[<e|E>[+|-]<exp>]`.
    ///
    /// The function returns an error in these cases:
    ///
    /// * An empty string has been given as `lit` -> `ParseDecimalError::Empty`
    /// * `lit` does not fit one of the two forms given above ->
    ///   `ParseDecimalError::Invalid`
    /// * The number of fractional digits in `lit` minus the value of the signed
    ///   exponent in `lit` exceeds the type parameter `P` ->
    ///   `ParseDecimalError::PrecLimitExceeded`
    /// * The given decimal literal exceeds the maximum value representable by
    ///   the type -> ParseDecimalError::MaxValueExceeded
    ///
    /// # Examples:
    ///
    /// ```rust
    /// # #![allow(incomplete_features)]
    /// # #![feature(generic_const_exprs)]
    /// # use rust_fixed_point_decimal::{Decimal, ParseDecimalError};
    /// # use std::str::FromStr;
    /// # fn main() -> Result<(), ParseDecimalError> {
    /// let d = Decimal::<4>::from_str("38.207")?;
    /// assert_eq!(d.to_string(), "38.2070");
    /// let d = Decimal::<7>::from_str("-132.0207e-2")?;
    /// assert_eq!(d.to_string(), "-1.3202070");
    /// # Ok(()) }
    /// ```
    fn from_str(lit: &str) -> Result<Self, Self::Err> {
        let prec = P as isize;
        let (coeff, exponent) = dec_repr_from_str(lit)?;
        if exponent > 0 {
            let shift = prec + exponent;
            if shift > 38 {
                // 10 ^ 39 > int128::MAX
                return Result::Err(ParseDecimalError::MaxValueExceeded);
            }
            match checked_mul_pow_ten(coeff, shift as u8) {
                None => Result::Err(ParseDecimalError::MaxValueExceeded),
                Some(coeff) => Ok(Self::new_raw(coeff)),
            }
        } else {
            let n_frac_digits = -exponent;
            match n_frac_digits.cmp(&prec) {
                Ordering::Equal => Ok(Self::new_raw(coeff)),
                Ordering::Less => {
                    let shift = prec - n_frac_digits;
                    match checked_mul_pow_ten(coeff, shift as u8) {
                        None => {
                            Result::Err(ParseDecimalError::MaxValueExceeded)
                        }
                        Some(coeff) => Ok(Self::new_raw(coeff)),
                    }
                }
                Ordering::Greater => {
                    Result::Err(ParseDecimalError::PrecLimitExceeded)
                }
            }
        }
    }
}

impl<const P: u8> TryFrom<&str> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    type Error = ParseDecimalError;

    #[inline]
    fn try_from(lit: &str) -> Result<Self, Self::Error> {
        Self::from_str(lit)
    }
}

#[cfg(test)]
mod tests {
    use std::{convert::TryFrom, str::FromStr};

    use rust_fixed_point_decimal_core::ParseDecimalError;

    use crate::Decimal;

    #[test]
    fn test_from_int_lit() {
        let d = Decimal::<4>::from_str("1957945").unwrap();
        assert_eq!(d.coeff, 19579450000);
    }

    #[test]
    fn test_from_int_lit_no_prec() {
        let d = Decimal::<0>::from_str("1957945").unwrap();
        assert_eq!(d.coeff, 1957945);
    }

    #[test]
    fn test_from_dec_lit() {
        let d = Decimal::<2>::from_str("-17.5").unwrap();
        assert_eq!(d.coeff, -1750);
    }

    #[test]
    fn test_from_frac_only_lit() {
        let d = Decimal::<7>::from_str("+.75").unwrap();
        assert_eq!(d.coeff, 7500000);
    }

    #[test]
    fn test_from_int_lit_neg_exp() {
        let d = Decimal::<5>::from_str("17e-5").unwrap();
        assert_eq!(d.coeff, 17);
    }

    #[test]
    fn test_from_int_lit_pos_exp() {
        let d = Decimal::<1>::from_str("+217e3").unwrap();
        assert_eq!(d.coeff, 2170000);
    }

    #[test]
    fn test_from_dec_lit_neg_exp() {
        let d = Decimal::<3>::from_str("-533.7e-2").unwrap();
        assert_eq!(d.coeff, -5337);
    }

    #[test]
    fn test_from_dec_lit_pos_exp() {
        let d = Decimal::<1>::from_str("700004.002E13").unwrap();
        assert_eq!(d.coeff, 70000400200000000000);
    }

    #[test]
    fn test_err_empty_str() {
        let res = Decimal::<2>::from_str("");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::Empty);
    }

    #[test]
    fn test_err_invalid_lit() {
        let lits = [" ", "+", "-4.33.2", "2.87 e3", "+e3", ".4e3 "];
        for lit in lits {
            let res = Decimal::<2>::from_str(lit);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, ParseDecimalError::Invalid);
        }
    }

    #[test]
    fn test_prec_limit_exceeded() {
        let res = Decimal::<2>::from_str("17.295");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::PrecLimitExceeded);
    }

    #[test]
    fn test_prec_limit_exceeded_with_exp() {
        let res = Decimal::<3>::from_str("17.4e-3");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::PrecLimitExceeded);
    }

    #[test]
    fn test_int_lit_max_val_dec0_exceeded() {
        let i = i128::MIN;
        let mut s = format!("{}", i);
        s.remove(0);
        let res = Decimal::<0>::from_str(&s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::MaxValueExceeded);
    }

    #[test]
    fn test_int_lit_max_val_dec2_exceeded() {
        let i = i128::MAX / 100 + 1;
        let s = format!("{}", i);
        let res = Decimal::<2>::from_str(&s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::MaxValueExceeded);
    }

    #[test]
    fn test_dec_lit_max_val_exceeded() {
        let s = "123456789012345678901234567890123.4567890";
        let res = Decimal::<7>::from_str(&s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::MaxValueExceeded);
    }

    #[test]
    fn test_parse() {
        let s = "+28.700";
        let res = s.parse::<Decimal<3>>();
        assert!(!res.is_err());
        let dec = res.unwrap();
        assert_eq!(dec.coeff, 28700);
    }

    #[test]
    fn test_parse_prec_limit_exceeded() {
        let s = "+28.7005";
        let res = s.parse::<Decimal<3>>();
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::PrecLimitExceeded);
    }

    #[test]
    fn test_try_from() {
        let s = "-534000.708";
        let res = Decimal::<4>::try_from(s);
        assert!(!res.is_err());
        let dec = res.unwrap();
        assert_eq!(dec.coeff, -5340007080);
    }

    #[test]
    fn test_try_from_prec_limit_exceeded() {
        let s = "+28.700500";
        let res = Decimal::<5>::try_from(s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::PrecLimitExceeded);
    }
}
