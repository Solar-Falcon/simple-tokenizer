# simple-tokenizer

A tiny no_std tokenizer with line & column tracking.

**Goals**:

* `no_std`, no allocations and zero/minimal dependencies.
* Be simple to use.
* Line/column tracking.
* Allow jumping to an arbitrary position in the source.
* Backtracking by default, i.e. if a function fails, it won't consume any input.

This *isn't* a parser combinator library and it won't ever become one.
There are plenty of other choices already.

## Example

```rust
use simple_tokenizer::*;

// A small parser that would parse function calls with number/ident arguments.
let source = r"function(123, other_argument, 456)";

let mut tokens = source.as_tokens(); // AsTokens is implemented for any AsRef<str>

let fn_name = tokens.take_while(|ch| ch.is_ascii_alphabetic() || ch == '_').to_string();

// Empty => there was nothing matching a function name
if fn_name.is_empty() {
    // use better error handling youself
    panic!("error at {}", tokens.position());
}

tokens.take_while(char::is_whitespace); // skip whitespace

let mut args = Vec::new();

if !tokens.token("(") {
    panic!("error at {}", tokens.position());
}

// if the call succeeded, than '(' is consumed
    
tokens.take_while(char::is_whitespace); // skip whitespace

// for the sake of simplicity, I'm gonna stop checking for empty strings
args.push(tokens.take_while(|ch| ch.is_ascii_alphanumeric() || ch == '_').to_string());
tokens.take_while(char::is_whitespace); // skip whitespace

while tokens.token(",") {
    tokens.take_while(char::is_whitespace); // skip whitespace
        
    args.push(tokens.take_while(|ch| ch.is_ascii_alphanumeric() || ch == '_').to_string());

    tokens.take_while(char::is_whitespace); // skip whitespace
}

if !tokens.token(")") {
    panic!("error at {}", tokens.position());
}

assert!(tokens.is_at_end());
assert_eq!(fn_name, "function");
assert_eq!(args.as_slice(), &["123", "other_argument", "456"]);
```
