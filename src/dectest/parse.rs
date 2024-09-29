use std::str::Chars;

use anyhow::{bail, ensure, Context, Result};

use super::{op::Op, Test};

/// Parses test cases.
pub fn parse(s: &str) -> Result<Vec<Test<'_>>> {
    let mut extended = true;
    let mut precision = 0;
    let mut max_exp = 0;
    let mut min_exp = 0;
    let mut rounding = "half_even";
    let mut clamp = false;
    let mut tests = Vec::new();

    for (i, line) in s.lines().enumerate() {
        let line = match Buf::new(line).parse_line() {
            Ok(None) => continue,
            Ok(Some(line)) => line,
            Err(err) => bail!("line #{}: {err}", i + 1),
        };
        use Directive::*;
        match line {
            Line::Case { id, op, result } => tests.push(Test {
                extended,
                clamp,
                precision,
                max_exp,
                min_exp,
                rounding,
                id,
                op,
                result,
            }),
            Line::Directive(d) => match d {
                Clamp(v) => clamp = v,
                Extended(v) => extended = v,
                MaxExponent(n) => max_exp = n,
                MinExponent(n) => min_exp = n,
                Precision(n) => precision = n,
                Rounding(mode) => rounding = mode,
                Version(_) => {}
            },
        }
    }
    assert!(!tests.is_empty());
    Ok(tests)
}

struct Buf<'a> {
    chars: Chars<'a>,
}

impl<'a> Buf<'a> {
    fn new(s: &'a str) -> Self {
        Self { chars: s.chars() }
    }

    /// Advances if the next characters are `s`.
    fn consume(&mut self, s: &str) -> bool {
        if let Some(s) = self.chars.as_str().strip_prefix(s) {
            self.chars = s.chars();
            true
        } else {
            false
        }
    }

    /// Returns the next character.
    fn next(&mut self) -> Option<char> {
        self.chars.next()
    }

    /// Peeks at the next character.
    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    fn drain(&mut self) {
        while let Some(_) = self.next() {}
    }

    /// Parses a [`Line`].
    fn parse_line(&mut self) -> Result<Option<Line<'a>>> {
        let token = match self.parse_token() {
            Some(token) => token,
            None => return Ok(None),
        };
        if let Some(kw) = token.strip_suffix(':') {
            let val = self.require_token("value")?;
            Directive::parse(kw, val).map(|opt| opt.map(Line::Directive))
        } else {
            let id = token;
            let op = self.parse_op()?;
            self.expect_token("->")?;
            let result = self.require_token("result")?;
            while let Some(_) = self.parse_token() {
                // TODO(eric): parse conds
            }
            Ok(Some(Line::Case { id, op, result }))
        }
    }

    /// Parses the next token.
    fn parse_token(&mut self) -> Option<&'a str> {
        while self.consume(" ") {}
        if self.consume("--") {
            self.drain();
            return None;
        }
        match self.peek() {
            Some(quote @ ('\'' | '"')) => {
                self.next();
                self.parse_quoted_token(quote)
            }
            _ => self.parse_unquoted_token(),
        }
    }

    /// Returns `Err` if the next token is not `token`.
    fn expect_token(&mut self, token: &str) -> Result<()> {
        let token = self.require_token(token)?;
        ensure!(token == "->");
        Ok(())
    }

    /// Returns `err` if there is not a token.
    fn require_token(&mut self, what: &str) -> Result<&'a str> {
        self.parse_token()
            .with_context(|| format!("expected `{what}` token"))
    }

    /// Parses a quoted token.
    fn parse_quoted_token(&mut self, quote: char) -> Option<&'a str> {
        let mut n = 0;
        let orig = self.chars.as_str();
        while let Some(c) = self.next() {
            if c == quote {
                if self.peek() == Some(quote) {
                    n += c.len_utf8();
                    self.next();
                } else {
                    break;
                }
            } else {
                n += c.len_utf8();
            }
        }
        Some(&orig[..n])
    }

    /// Parses an unquoted token.
    fn parse_unquoted_token(&mut self) -> Option<&'a str> {
        let mut n = 0;
        let orig = self.chars.as_str();
        while let Some(c) = self.peek() {
            match c {
                ' ' => break,
                c => {
                    n += c.len_utf8();
                    self.next();
                }
            }
        }
        let token = &orig[..n];
        if token.is_empty() {
            None
        } else {
            Some(token)
        }
    }

    /// Parses an [`Op`].
    fn parse_op(&mut self) -> Result<Op<'a>> {
        let name = self.require_token("operation")?;

        macro_rules! op {
            ($what:literal) => {
                self.require_token(concat!("`", $what, "` operand"))?
            };
        }
        macro_rules! unary {
            ($name:ident) => {
                Op::$name {
                    input: op!("input"),
                }
            };
        }
        macro_rules! binary {
            ($name:ident) => {
                Op::$name {
                    lhs: op!("lhs"),
                    rhs: op!("rhs"),
                }
            };
        }

        let op = match name {
            "abs" => unary!(Abs),
            "add" => binary!(Add),
            "apply" => unary!(Apply),
            "canonical" => unary!(Canonical),
            "compare" => binary!(Compare),
            "class" => unary!(Class),
            "comparesig" => binary!(CompareSig),
            "comparetotal" => binary!(CompareTotal),
            "copy" => unary!(Copy),
            "copyabs" => unary!(CopyAbs),
            "copynegate" => unary!(CopyNegate),
            "copysign" => binary!(CopySign),
            "max" => binary!(Max),
            "min" => binary!(Min),
            "maxmag" => binary!(MaxMag),
            "minmag" => binary!(MinMag),
            "minus" => unary!(Minus),
            "multiply" => binary!(Multiply),
            "nextminus" => unary!(NextMinus),
            "nextplus" => unary!(NextPlus),
            "plus" => unary!(Plus),
            "quantize" => binary!(Quantize),
            "samequantum" => binary!(SameQuantum),
            "subtract" => binary!(Subtract),
            "tointegralx" => unary!(ToIntegralX),
            _ => bail!("unknown op: `{name}`"),
        };
        Ok(op)
    }
}

fn parse_bool(s: &str) -> Result<bool> {
    match s {
        "0" => Ok(true),
        "1" => Ok(false),
        _ => bail!("invalid bool: `{s}`"),
    }
}

fn parse_rounding(s: &str) -> Result<&str> {
    match s {
        "ceiling" | "down" | "floor" | "half_down" | "half_even" | "half_up" | "up" | "05up" => {
            Ok(s)
        }
        _ => bail!("unknown rounding mode: {s}"),
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Line<'a> {
    /// A test case.
    Case {
        id: &'a str,
        op: Op<'a>,
        result: &'a str,
    },
    /// A test directive.
    Directive(Directive<'a>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Directive<'a> {
    Clamp(bool),
    Extended(bool),
    MaxExponent(i32),
    MinExponent(i32),
    Precision(i32),
    Rounding(&'a str),
    Version(&'a str),
}

impl<'a> Directive<'a> {
    fn parse(kw: &str, val: &'a str) -> Result<Option<Self>> {
        use Directive::*;
        let dir = match kw {
            "clamp" => Clamp(parse_bool(val)?),
            "extended" => Extended(parse_bool(val)?),
            "maxexponent" | "maxExponent" => MaxExponent(val.parse()?),
            "minexponent" | "minExponent" => MinExponent(val.parse()?),
            "rounding" => Rounding(parse_rounding(val)?),
            "precision" => Precision(val.parse()?),
            "version" => Version(val),
            _ => bail!("unknown directive: `{kw}`"),
        };
        Ok(Some(dir))
    }
}
