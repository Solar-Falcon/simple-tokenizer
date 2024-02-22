use crate::{Offset, Position, Tokens};
use core::{ops::Deref, str::FromStr};

/// A type holding the byte offset as well as position info.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Location {
    offset: Offset,
    pos: Position,
}

impl Location {
    /// Get the position info.
    #[inline]
    pub fn position(&self) -> Position {
        self.pos
    }
}

impl yap::TokenLocation for Location {
    #[inline]
    fn offset(&self) -> usize {
        self.offset.0
    }
}

impl<'s> yap::Tokens for Tokens<'s> {
    type Item = char;
    type Location = Location;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.char()
    }

    #[inline]
    fn location(&self) -> Self::Location {
        Location {
            offset: Offset(self.offset),
            pos: self.pos,
        }
    }

    #[inline]
    fn set_location(&mut self, location: Self::Location) {
        self.set_offset(location.offset);
    }

    #[inline]
    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.offset == location.offset.0 && self.pos == location.pos
    }

    #[inline]
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as FromStr>::Err>
    where
        Out: FromStr,
        Buf: FromIterator<Self::Item> + Deref<Target = str>,
    {
        let result = self.remaining_input.parse()?;

        self.consume_all();

        Ok(result)
    }

    #[inline]
    fn peek(&mut self) -> Option<Self::Item> {
        self.remaining_input.chars().next()
    }
}

impl<'s> yap::IntoTokens<char> for Tokens<'s> {
    type Tokens = Self;

    #[inline]
    fn into_tokens(self) -> Self::Tokens {
        self
    }
}
