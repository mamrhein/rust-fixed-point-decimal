// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::fmt::{Debug, Display, Formatter};

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
    NotANumber,
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
            DecimalError::NotANumber => "Given value is not a number.",
        }
    }
}

impl Display for DecimalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self._description(), f)
    }
}

impl std::error::Error for DecimalError {}
