// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::fmt::{Display, Formatter};

use crate::powers_of_ten::checked_mul_pow_ten;

/// An error which can be returned when parsing a decimal literal.
///
/// This error is used as the error type for the `FromStr` implementation of
/// `Decimal<P>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseDecimalError {
    /// An empty string has been given as literal.
    Empty,
    /// The given string is not a valid decimal literal.
    Invalid,
    /// The given decimal literal has more fractional digits than specified by
    /// the type parameter `P`.
    PrecLimitExceeded,
    /// The given decimal literal would exceed the maximum value representable
    /// by the type.
    MaxValueExceeded,
}

impl ParseDecimalError {
    #[doc(hidden)]
    pub fn _description(&self) -> &str {
        match self {
            ParseDecimalError::Empty => "Empty string.",
            ParseDecimalError::Invalid => "Invalid decimal string literal.",
            ParseDecimalError::PrecLimitExceeded => {
                "Too many fractional digits."
            }
            ParseDecimalError::MaxValueExceeded => {
                "Maximum representable value exceeded."
            }
        }
    }
}

impl Display for ParseDecimalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self._description(), f)
    }
}

impl std::error::Error for ParseDecimalError {}

struct DecLitParts<'a> {
    num_sign: &'a str,
    int_part: &'a str,
    frac_part: &'a str,
    exp_sign: &'a str,
    exp_part: &'a str,
}

/// Parse a Decimal literal in the form
/// \[+|-]<int>\[.<frac>]\[<e|E>\[+|-]<exp>] or
/// \[+|-].<frac>\[<e|E>\[+|-]<exp>].
fn parse_decimal_literal(lit: &str) -> Result<DecLitParts, ParseDecimalError> {
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
                        frac_part: "",
                        exp_sign: "",
                        exp_part: "",
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
                        exp_sign: "",
                        exp_part: "",
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

/// Convert a decimal number literal into a representation in the form
/// (coefficient, exponent), so that number == coefficient * 10 ^ exponent.
///
/// The literal must be in the form
/// \[+|-]<int>\[.<frac>]\[<e|E>\[+|-]<exp>] or
/// \[+|-].<frac>\[<e|E>\[+|-]<exp>].
#[doc(hidden)]
pub fn dec_repr_from_str(
    lit: &str,
) -> Result<(i128, isize), ParseDecimalError> {
    let max_prec = crate::MAX_PREC as isize;
    let parts = parse_decimal_literal(lit)?;
    let exp: isize = if parts.exp_part.len() > 0 {
        if parts.exp_sign == "-" {
            -parts.exp_part.parse::<isize>().unwrap()
        } else {
            parts.exp_part.parse().unwrap()
        }
    } else {
        0
    };
    let n_frac_digits = parts.frac_part.len() as isize;
    if n_frac_digits - exp > max_prec {
        return Result::Err(ParseDecimalError::PrecLimitExceeded);
    }
    let mut coeff: i128 = if parts.int_part.len() > 0 {
        match parts.int_part.parse() {
            Err(_) => {
                return Err(ParseDecimalError::MaxValueExceeded);
            }
            Ok(i) => i,
        }
    } else {
        0
    };
    if n_frac_digits > 0 {
        match checked_mul_pow_ten(coeff, n_frac_digits as u8) {
            None => return Result::Err(ParseDecimalError::MaxValueExceeded),
            Some(val) => coeff = val,
        }
        coeff += parts.frac_part.parse::<i128>().unwrap();
    }
    if parts.num_sign == "-" {
        Ok((-coeff, exp - n_frac_digits))
    } else {
        Ok((coeff, exp - n_frac_digits))
    }
}
