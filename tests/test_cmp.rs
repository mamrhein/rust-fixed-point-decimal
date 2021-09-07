// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#[cfg(test)]
mod tests {
    use rust_fixed_point_decimal::{Dec, Decimal};

    #[test]
    fn test_ordering() {
        let test_data = [
            Decimal::<1>::MIN,
            Dec!(-3481900.3),
            Dec!(-0.4),
            Decimal::<1>::ZERO,
            Dec!(0.2),
            Decimal::<1>::ONE,
            Dec!(17.0),
            Decimal::<1>::MAX,
        ];
        for (i, x) in test_data.iter().enumerate() {
            for (j, y) in test_data.iter().enumerate() {
                assert_eq!(x.cmp(&y), i.cmp(&j));
            }
        }
    }
}
