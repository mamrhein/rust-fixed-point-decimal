// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::fmt::{Debug, Display, Formatter};

/// An error which can be returned when parsing a decimal literal.
///
/// This error is used as the error type for the [`FromStr`] implementation of
/// [`Decimal<P>`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseDecimalError {
    Empty,
    Invalid,
    PrecLimitExceeded,
    MaxValueExceeded,
}

impl ParseDecimalError {
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

/// An error which can be returned from converting numbers to Decimal or from
/// binary operators on Decimal.
///
/// This error is used as the error type for the [`TryFrom`] implementation of
/// [`Decimal<P>`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecimalError {
    PrecLimitExceeded,
    MaxValueExceeded,
    InfiniteValue,
}

impl DecimalError {
    pub fn _description(&self) -> &str {
        match self {
            DecimalError::PrecLimitExceeded => {
                "Result exceeds the precision limit."
            }
            DecimalError::MaxValueExceeded => {
                "Maximum representable value exceeded."
            }
            DecimalError::InfiniteValue => {
                "Can't convert infinite value to Decimal."
            }
        }
    }
}

impl Display for DecimalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self._description(), f)
    }
}

impl std::error::Error for DecimalError {}
