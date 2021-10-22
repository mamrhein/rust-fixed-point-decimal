// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use ::proc_macro::TokenStream;
use ::quote::quote;
use rust_fixed_point_decimal_core::{
    dec_repr_from_str, ParseDecimalError, MAX_PREC,
};

/// Macro used to convert a number literal into a Decimal\<P\>.
///
/// The literal must be in the form
/// \[+|-]\<int\>\[.\<frac\>]\[<e|E>\[+|-]\<exp\>] or
/// \[+|-].\<frac\>\[<e|E>\[+|-]\<exp\>].
///
/// P is determined by the number of fractional digits minus the value of the
/// signed exponent. It must not exceed the constant MAX_PREC.
///
/// The resulting value must not exceed the limits given by Decimal::\<P\>::MIN
/// and Decimal::\<P\>::MAX.
///
/// # Panics
///
/// The macro panics if the conditions listed above are not met!
///
/// # Examples
///
/// ```ignore
/// let d = Dec!(17.5);
/// assert_eq!(d.to_string(), "17.5");
///
/// let d = Dec!(-170.5e-2);
/// assert_eq!(d.to_string(), "-1.705");
/// ```
#[allow(non_snake_case)]
#[proc_macro]
pub fn Dec(input: TokenStream) -> TokenStream {
    let mut src = input.to_string();
    // "-" and "+" get separated by a blank => remove it
    if src.starts_with("- ") || src.starts_with("+ ") {
        src.remove(1);
    }

    match dec_repr_from_str(&src) {
        Err(e) => panic!("{}", e),
        Ok((mut coeff, mut exponent)) => {
            if -exponent > (MAX_PREC as isize) {
                panic!("{}", ParseDecimalError::PrecLimitExceeded)
            }
            if exponent > 38 {
                // 10 ^ 39 > int128::MAX
                panic!("{}", ParseDecimalError::MaxValueExceeded);
            }
            if exponent > 0 {
                match coeff.checked_mul(10i128.pow(exponent as u32)) {
                    None => panic!("{}", ParseDecimalError::MaxValueExceeded),
                    Some(val) => {
                        coeff = val;
                    }
                }
                exponent = 0;
            }
            let prec = -exponent as u8;
            quote!(
                rust_fixed_point_decimal::Decimal::<#prec>
                ::new_raw(#coeff)
            )
            .into()
        }
    }
}
