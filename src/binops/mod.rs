// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

// implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are Decimal<P> and Decimal<Q>

macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a, const P: u8, const Q: u8> $imp<Decimal<Q>> for &'a Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>>,
        {
            type Output = <Decimal<P> as $imp<Decimal<Q>>>::Output;

            #[inline]
            fn $method(self, other: Decimal<Q>) -> Self::Output {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8, const Q: u8> $imp<&Decimal<Q>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>>,
        {
            type Output = <Decimal<P> as $imp<Decimal<Q>>>::Output;

            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Self::Output {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8, const Q: u8> $imp<&Decimal<Q>> for &Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>>,
        {
            type Output = <Decimal<P> as $imp<Decimal<Q>>>::Output;

            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Self::Output {
                $imp::$method(*self, *other)
            }
        }
    };
}

macro_rules! forward_ref_binop_rounded {
    (impl $imp:ident, $method:ident) => {
        impl<'a, const P: u8, const Q: u8, const R: u8>
            $imp<Decimal<Q>, Decimal<R>> for &'a Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>, Decimal<R>>,
        {
            #[inline]
            fn $method(self, other: Decimal<Q>) -> Decimal<R> {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8, const Q: u8, const R: u8>
            $imp<&Decimal<Q>, Decimal<R>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>, Decimal<R>>,
        {
            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Decimal<R> {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8, const Q: u8, const R: u8>
            $imp<&Decimal<Q>, Decimal<R>> for &Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>, Decimal<R>>,
        {
            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Decimal<R> {
                $imp::$method(*self, *other)
            }
        }
    };
}

mod add_sub;
mod cmp;
mod div;
pub mod div_rounded;
mod mul;
pub mod mul_rounded;
