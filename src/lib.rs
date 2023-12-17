#![no_std]
#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))]
#![warn(missing_docs)]

use core::fmt::{self, Display};

/// Byte range in the source input.
pub type Span = core::ops::Range<usize>;

/// Position (line & column) in the source input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position {
    /// Line count
    pub line: u32,
    /// Column count
    pub column: u32,
}

impl Position {
    /// Starting position (line = 1, column = 1).
    #[inline]
    pub const fn starting() -> Self {
        Position { line: 1, column: 1 }
    }

    /// Updates the position.
    /// If ch == '\n', increases line count and resets column count,
    /// otherwise just increases column count.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::Position;
    ///
    /// let mut pos = Position::starting();
    ///
    /// assert_eq!(pos.update_from_char(' '), Position { line: 1, column: 2 });
    /// assert_eq!(pos.update_from_char('\n'), Position { line: 2, column: 1 });
    ///
    /// ```
    pub fn update_from_char(&mut self, ch: char) -> Self {
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }

        *self
    }

    /// Updates the position.
    /// Identical to calling `update_from_char()` for every character of the string.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::Position;
    ///
    /// let mut pos = Position::starting();
    ///
    /// assert_eq!(pos.update_from_str("line 1\nline 2\nlong line 3"), Position { line: 3, column: 12 });
    ///
    /// ```
    pub fn update_from_str(&mut self, s: &str) -> Self {
        let mut last_pos = 0;

        let lines = s
            .bytes()
            .enumerate()
            .filter(|(i, byte)| {
                if *byte == b'\n' {
                    last_pos = *i;
                    true
                } else {
                    false
                }
            })
            .count() as u32;

        self.line += lines;

        let col = s[last_pos..].chars().count() as u32;
        self.column = col;

        *self
    }
}

impl Display for Position {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[line {}, col{}]", self.line, self.column)
    }
}

/// Byte offset in the source input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Offset(pub usize);

/// Tokens instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tokens<'s> {
    full_input: &'s str,
    remaining_input: &'s str,
    span: Span,
    pos: Position,
    offset: usize,
}

impl<'s> Tokens<'s> {
    /// Construct a new instance from a string slice.
    #[inline]
    pub fn new(input: &'s str) -> Self {
        Self {
            full_input: input,
            remaining_input: input,
            span: 0..0,
            pos: Position::starting(),
            offset: 0,
        }
    }

    /// Returns the original full input.
    #[inline]
    pub fn input(&self) -> &str {
        self.full_input
    }

    /// Part of the input string that hasn't been consumed yet.
    #[inline]
    pub fn remainder(&self) -> &str {
        self.remaining_input
    }

    /// Byte span of the last token.
    #[inline]
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    /// Current position (just after the last token).
    #[inline]
    pub fn position(&self) -> Position {
        self.pos
    }

    /// Current byte offset in the source.
    #[inline]
    pub fn offset(&self) -> Offset {
        Offset(self.offset)
    }

    /// Sets the offset if it is valid, updating position and span.
    /// Returns `true` if the offset is valid, `false` otherwise.
    pub fn set_offset(&mut self, offset: Offset) -> bool {
        let offset = offset.0;

        if self.full_input.is_char_boundary(offset) {
            self.remaining_input = &self.full_input[offset..];

            self.span = offset..offset;
            self.pos = Position::starting().update_from_str(&self.full_input[..offset]);
            self.offset = offset;
            true
        } else {
            false
        }
    }

    /// Returns `true` if the current position is the start of input.
    #[inline]
    pub fn is_at_start(&self) -> bool {
        self.offset == 0
    }

    /// Returns `true` if the input has been exhausted.
    #[inline]
    pub fn is_at_end(&self) -> bool {
        self.remaining_input.is_empty()
    }

    /// Peeks at the next character of the input.
    #[inline]
    pub fn peek(&self) -> Option<char> {
        self.remaining_input.chars().next()
    }

    /// Consumes the rest of input.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "tokens".as_tokens();
    ///
    /// assert_eq!(tokens.consume_all(), "tokens");
    /// assert!(tokens.remainder().is_empty());
    ///
    /// ```
    #[inline]
    pub fn consume_all(&mut self) -> &str {
        self.split(self.remaining_input.len())
    }

    /// Consume the next substring equal to `token` or nothing.
    /// Basically a shortcut for `bytes_if(token.len(), |s| s == token).is_some()`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "tok1 tok2".as_tokens();
    ///
    /// assert!(tokens.token("tok1"));
    /// assert_eq!(tokens.remainder(), " tok2");
    ///
    /// assert!(!tokens.token(" tok3"));
    /// assert_eq!(tokens.remainder(), " tok2");
    ///
    /// ```
    pub fn token(&mut self, token: impl AsRef<str>) -> bool {
        let token = token.as_ref();

        self.remaining_input
            .get(..token.len())
            .filter(|s| *s == token)
            .map(|s| self.split(s.len()))
            .is_some()
    }

    /// Try to consume a substring equal to one of the provided tokens.
    /// Returns the first successful substring.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "tok1 tok2".as_tokens();
    ///
    /// assert_eq!(tokens.tokens(&["tok", "tok1"]), Some("tok"));
    /// assert_eq!(tokens.remainder(), "1 tok2");
    ///
    /// assert_eq!(tokens.tokens(&["1 tok3", "2 tok2"]), None);
    /// assert_eq!(tokens.remainder(), "1 tok2");
    ///
    /// ```
    pub fn tokens(&mut self, tokens: impl IntoIterator<Item = impl AsRef<str>>) -> Option<&str> {
        for token in tokens.into_iter() {
            if self.token(token) {
                return Some(&self.full_input[self.span.clone()]);
            }
        }

        None
    }

    /// Consume the next character.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "tokens".as_tokens();
    ///
    /// assert_eq!(tokens.char(), Some('t'));
    /// assert_eq!(tokens.remainder(), "okens");
    ///
    /// ```
    pub fn char(&mut self) -> Option<char> {
        (!self.remaining_input.is_empty()).then(|| self.split_next_char())
    }

    /// Consume the next character if it matches a predicate.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "tokens".as_tokens();
    ///
    /// assert_eq!(tokens.char_if(char::is_alphabetic), Some('t'));
    /// assert_eq!(tokens.remainder(), "okens");
    ///
    /// assert_eq!(tokens.char_if(char::is_numeric), None);
    /// assert_eq!(tokens.remainder(), "okens");
    ///
    /// ```
    pub fn char_if(&mut self, f: impl FnOnce(char) -> bool) -> Option<char> {
        self.remaining_input
            .chars()
            .next()
            .filter(|ch| f(*ch))
            .map(|_| self.split_next_char())
    }

    /// Consume the next `n` bytes.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "tokens123".as_tokens();
    ///
    /// assert_eq!(tokens.bytes(6), Some("tokens"));
    /// assert_eq!(tokens.remainder(), "123");
    ///
    /// assert_eq!(tokens.bytes(5), None);
    /// assert_eq!(tokens.remainder(), "123");
    ///
    /// ```
    pub fn bytes(&mut self, n: usize) -> Option<&str> {
        self.remaining_input
            .is_char_boundary(n)
            .then(|| self.split(n))
    }

    /// Consume the next `n` bytes if they match a predicate.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "1231234".as_tokens();
    ///
    /// assert_eq!(tokens.bytes_if(3, |s| s.chars().all(char::is_numeric)), Some("123"));
    /// assert_eq!(tokens.remainder(), "1234");
    ///
    /// assert_eq!(tokens.bytes_if(5, |s| s.chars().all(char::is_numeric)), None);
    /// assert_eq!(tokens.remainder(), "1234");
    ///
    /// ```
    pub fn bytes_if(&mut self, n: usize, f: impl FnOnce(&str) -> bool) -> Option<&str> {
        self.remaining_input
            .get(..n)
            .filter(|s| f(s))
            .map(|s| self.split(s.len()))
    }

    /// Consume the next `n` characters.
    /// Doesn't advance if there aren't enough characters left.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "tokens123".as_tokens();
    ///
    /// assert_eq!(tokens.chars(6), Some("tokens"));
    /// assert_eq!(tokens.remainder(), "123");
    ///
    /// assert_eq!(tokens.chars(5), None);
    /// assert_eq!(tokens.remainder(), "123");
    ///
    /// ```
    pub fn chars(&mut self, n: usize) -> Option<&str> {
        self.remaining_input
            .char_indices()
            .nth(n.checked_sub(1)?)
            .map(|(i, ch)| self.split(i + ch.len_utf8()))
    }

    /// Consume the next `n` characters if they match a predicate.
    /// Doesn't advance if there aren't enough characters left.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "1231234".as_tokens();
    ///
    /// assert_eq!(tokens.chars_if(3, |s| s.chars().all(char::is_numeric)), Some("123"));
    /// assert_eq!(tokens.remainder(), "1234");
    ///
    /// assert_eq!(tokens.chars_if(5, |s| s.chars().all(char::is_numeric)), None);
    /// assert_eq!(tokens.remainder(), "1234");
    ///
    /// ```
    pub fn chars_if(&mut self, n: usize, f: impl FnOnce(&str) -> bool) -> Option<&str> {
        self.remaining_input
            .char_indices()
            .nth(n.checked_sub(1)?)
            .map(|(i, ch)| &self.remaining_input[..i + ch.len_utf8()])
            .filter(|s| f(s))
            .map(|s| self.split(s.len()))
    }

    /// Consume characters while `f` returns true.
    /// Returns the consumed substring.
    ///
    /// # Example
    ///
    /// ```rust
    /// use simple_tokenizer::*;
    ///
    /// let mut tokens = "12345word".as_tokens();
    ///
    /// assert_eq!(tokens.take_while(char::is_numeric), "12345");
    /// assert_eq!(tokens.remainder(), "word");
    ///
    /// ```
    pub fn take_while(&mut self, mut f: impl FnMut(char) -> bool) -> &str {
        self.remaining_input
            .char_indices()
            .take_while(|(_, ch)| f(*ch))
            .last()
            .map(|(i, ch)| self.split(i + ch.len_utf8()))
            .unwrap_or("")
    }

    fn split(&mut self, i: usize) -> &str {
        let (result, remainder) = self.remaining_input.split_at(i);

        self.remaining_input = remainder;

        self.pos.update_from_str(result);

        self.offset += i;
        self.span = self.span.end..self.offset;

        result
    }

    fn split_next_char(&mut self) -> char {
        let ch = self.remaining_input.chars().next().unwrap();

        self.remaining_input = &self.remaining_input[ch.len_utf8()..];

        self.offset += ch.len_utf8();
        self.span = self.span.end..self.offset;

        self.pos.update_from_char(ch);

        ch
    }
}

/// Convenience trait implemented for every `T: AsRef<str>`.
pub trait AsTokens {
    /// Convenient converting to tokens instance.
    fn as_tokens(&self) -> Tokens<'_>;
}

impl<T> AsTokens for T
where
    T: AsRef<str>,
{
    #[inline]
    fn as_tokens(&self) -> Tokens {
        Tokens::new(self.as_ref())
    }
}
