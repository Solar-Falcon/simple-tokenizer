use crate::{AsTokens, Offset, Position, Tokens};
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

/// Wrapper around `Tokens` that implements `yap::Tokens`.
/// 
/// Separate struct to avoid confusion, since both have a few similar (or outright identical)
/// method names that may not work as identically as their names might suggest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct YapTokens<'s> {
    /// Underlying `Tokens` object.
    pub simple_tokens: Tokens<'s>,
}

impl<'s> From<Tokens<'s>> for YapTokens<'s> {
    #[inline]
    fn from(simple_tokens: Tokens<'s>) -> Self {
        YapTokens { simple_tokens }
    }
}

impl<'s> yap::Tokens for YapTokens<'s> {
    type Item = char;
    type Location = Location;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.simple_tokens.char()
    }

    #[inline]
    fn location(&self) -> Self::Location {
        Location {
            offset: Offset(self.simple_tokens.offset),
            pos: self.simple_tokens.pos,
        }
    }

    #[inline]
    fn set_location(&mut self, location: Self::Location) {
        self.simple_tokens.set_offset(location.offset);
    }

    #[inline]
    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.simple_tokens.offset == location.offset.0 && self.simple_tokens.pos == location.pos
    }

    #[inline]
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as FromStr>::Err>
    where
        Out: FromStr,
        Buf: FromIterator<Self::Item> + Deref<Target = str>,
    {
        let result = self.simple_tokens.remaining_input.parse()?;

        self.simple_tokens.consume_all();

        Ok(result)
    }

    #[inline]
    fn peek(&mut self) -> Option<Self::Item> {
        self.simple_tokens.peek()
    }
}

impl<'s> yap::IntoTokens<char> for YapTokens<'s> {
    type Tokens = Self;

    #[inline]
    fn into_tokens(self) -> Self::Tokens {
        self
    }
}

impl<'s> AsTokens for YapTokens<'s> {
    #[inline]
    fn as_tokens(&self) -> Tokens<'_> {
        self.simple_tokens.as_tokens()
    }
}
