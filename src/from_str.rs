// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::str::FromStr;

use crate::{
    errors::ParseDecimalError, powers_of_ten::checked_mul_pow_ten, Decimal,
    PrecLimitCheck, True,
};

pub(crate) struct DecLitParts<'a> {
    num_sign: &'a str,
    int_part: &'a str,
    frac_part: &'a str,
    exp_sign: &'a str,
    exp_part: &'a str,
}

/// Parse a Decimal literal in the form
/// \[+|-]<int>\[.<frac>]\[<e|E>\[+|-]<exp>] or
/// \[+|-].<frac>\[<e|E>\[+|-]<exp>].
pub(crate) fn parse_decimal_literal(
    lit: &str,
) -> Result<DecLitParts, ParseDecimalError> {
    let mut num_sign_range = 0usize..0usize;
    let mut int_part_range = 0usize..0usize;
    let mut frac_part_range = 0usize..0usize;
    let mut exp_sign_range = 0usize..0usize;
    let mut exp_part_range = 0usize..0usize;
    let mut chars = lit.char_indices();
    let mut next = chars.next();
    if let None = next {
        return Result::Err(ParseDecimalError::Empty);
    }
    let (mut curr_idx, mut curr_char) = next.unwrap();
    if curr_char == '-' || curr_char == '+' {
        num_sign_range = curr_idx..curr_idx + 1;
        next = chars.next();
    }
    int_part_range.start = num_sign_range.end;
    loop {
        match next {
            None => {
                curr_idx = lit.len();
                if int_part_range.start < curr_idx {
                    int_part_range.end = lit.len();
                    return Ok(DecLitParts {
                        num_sign: &lit[num_sign_range],
                        int_part: &lit[int_part_range],
                        frac_part: &lit[frac_part_range],
                        exp_sign: &lit[exp_sign_range],
                        exp_part: &lit[exp_part_range],
                    });
                } else {
                    return Result::Err(ParseDecimalError::Invalid);
                }
            }
            Some((idx, ch)) => {
                if !ch.is_digit(10) {
                    int_part_range.end = idx;
                    curr_char = ch;
                    curr_idx = idx;
                    break;
                }
            }
        }
        next = chars.next();
    }
    if curr_char == '.' {
        frac_part_range.start = curr_idx + 1;
        next = chars.next();
        loop {
            match next {
                None => {
                    frac_part_range.end = lit.len();
                    return Ok(DecLitParts {
                        num_sign: &lit[num_sign_range],
                        int_part: &lit[int_part_range],
                        frac_part: &lit[frac_part_range],
                        exp_sign: &lit[exp_sign_range],
                        exp_part: &lit[exp_part_range],
                    });
                }
                Some((idx, ch)) => {
                    if !ch.is_digit(10) {
                        frac_part_range.end = idx;
                        curr_char = ch;
                        break;
                    }
                }
            }
            next = chars.next();
        }
    }
    if curr_char == 'e' || curr_char == 'E' {
        next = chars.next();
        if let None = next {
            return Result::Err(ParseDecimalError::Invalid);
        }
        let (curr_idx, curr_char) = next.unwrap();
        if curr_char == '-' || curr_char == '+' {
            exp_sign_range = curr_idx..curr_idx + 1;
            exp_part_range.start = curr_idx + 1;
        } else if curr_char.is_digit(10) {
            exp_part_range.start = curr_idx;
        } else {
            return Result::Err(ParseDecimalError::Invalid);
        }
        next = chars.next();
        loop {
            match next {
                None => {
                    exp_part_range.end = lit.len();
                    break;
                }
                Some((_, ch)) => {
                    if !ch.is_digit(10) {
                        return Result::Err(ParseDecimalError::Invalid);
                    }
                }
            }
            next = chars.next();
        }
    } else {
        return Result::Err(ParseDecimalError::Invalid);
    }
    if int_part_range.len() == 0 && frac_part_range.len() == 0 {
        return Result::Err(ParseDecimalError::Invalid);
    }
    Ok(DecLitParts {
        num_sign: &lit[num_sign_range],
        int_part: &lit[int_part_range],
        frac_part: &lit[frac_part_range],
        exp_sign: &lit[exp_sign_range],
        exp_part: &lit[exp_part_range],
    })
}

impl<const P: u8> FromStr for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    type Err = ParseDecimalError;

    /// Convert a number literal into a Decimal<P>.
    ///
    /// The literal must be in the form
    /// \[+|-]<int>\[.<frac>]\[<e|E>\[+|-]<exp>] or
    /// \[+|-].<frac>\[<e|E>\[+|-]<exp>].
    fn from_str(lit: &str) -> Result<Self, Self::Err> {
        let prec = P as isize;
        let parts = parse_decimal_literal(lit)?;
        let exp: isize = if parts.exp_part.len() > 0 {
            if parts.exp_sign == "-" {
                parts.exp_part.parse::<isize>().unwrap() * -1
            } else {
                parts.exp_part.parse().unwrap()
            }
        } else {
            0
        };
        let n_frac_digits = parts.frac_part.len() as isize;
        if n_frac_digits - exp > prec {
            return Result::Err(ParseDecimalError::PrecLimitExceeded);
        }
        let mut significant: i128 = if parts.int_part.len() > 0 {
            parts.int_part.parse().unwrap()
        } else {
            0
        };
        if n_frac_digits > 0 {
            match checked_mul_pow_ten(significant, n_frac_digits as u8) {
                None => {
                    return Result::Err(ParseDecimalError::MaxValueExceeded)
                }
                Some(val) => significant = val,
            }
            significant += parts.frac_part.parse::<i128>().unwrap();
        }
        let shift = prec - n_frac_digits + exp;
        if shift > 0 {
            match checked_mul_pow_ten(significant, shift as u8) {
                None => {
                    return Result::Err(ParseDecimalError::MaxValueExceeded)
                }
                Some(val) => significant = val,
            }
        }
        if parts.num_sign == "-" {
            Ok(Self::new_raw(-significant))
        } else {
            Ok(Self::new_raw(significant))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::{errors::ParseDecimalError, Decimal};

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
        let res = Decimal::<3>::from_str("17e-5");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::PrecLimitExceeded);
    }

    #[test]
    fn test_int_lit_max_val_exceeded() {
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
}
