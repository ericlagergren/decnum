use anyhow::{bail, Context, Result};

use super::{op::Op, Test};
use crate::ctx::RoundingMode;

/// Parses test cases.
pub fn parse(s: &str) -> Result<Vec<Test<'_>>> {
    let mut extended = 1;
    let mut precision: u32 = 0;
    let mut max_exp: i16 = 0;
    let mut min_exp: i16 = 0;
    let mut rounding: RoundingMode = RoundingMode::default();
    let mut clamp = 0;
    let mut cases = Vec::new();
    for (i, line) in s.lines().enumerate() {
        if line.is_empty() {
            continue;
        }

        if line.starts_with("--") {
            // A comment.
            continue;
        }

        if let Some((_, _)) = line.split_once("version: ") {
            continue;
        }

        if let Some((_, v)) = line.split_once("precision: ") {
            precision = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse precision: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("rounding: ") {
            rounding = RoundingMode::try_from_str(v.trim())
                .with_context(|| format!("#{i}: invalid rounding mode: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("maxExponent: ") {
            max_exp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `maxExponent`: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("minExponent: ") {
            min_exp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `minExponent`: `{v}`"))?;
            continue;
        }
        if let Some((_, v)) = line.split_once("minexponent: ") {
            min_exp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `minexponent`: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("extended: ") {
            extended = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `extended`: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("clamp: ") {
            clamp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `clamp`: `{v}`"))?;
            continue;
        }

        //println!("line = {line}");
        let (name, rest) = line
            .split_once(" ")
            .with_context(|| format!("#{i}: test case missing name: `{line}`"))?;
        let (op, rest) = Op::parse(rest.trim())
            .with_context(|| format!("#{i}: unable to parse op: `{rest}`"))?;
        let _ = rest; // TODO: conds
        let case = Test {
            extended: extended == 1,
            clamp: clamp == 1,
            precision,
            max_exp,
            min_exp,
            rounding,
            id: name,
            op,
        };
        cases.push(case);
    }
    assert!(!cases.is_empty());
    Ok(cases)
}

struct Buf<'a> {
    s: &'a str,
}

impl<'a> Buf<'a> {
    fn consume(&mut self, s: &str) -> bool {
        if let Some(s) = self.s.strip_prefix(s) {
            self.s = s;
            true
        } else {
            false
        }
    }

    fn peek(&self) -> Option<char> {
        self.s.chars().next()
    }

    fn parse_line(&mut self) -> Result<Option<Line<'a>>> {
        let token = match self.parse_token() {
            Some(token) => token,
            None => return Ok(None),
        };
        if let Some(kw) = token.strip_suffix(':') {
            todo!()
        } else {
            let id = token;
            let op = self.parse_op()?;
            todo!()
        }
    }

    fn parse_token(&mut self) -> Option<&'a str> {
        self.s = self.s.trim_start();
        if self.consume("--") {
            self.s = "";
            return None;
        }
        match self.peek() {
            Some(quote @ ('\'' | '"')) => {
                self.s = &self.s[1..];
                self.parse_quoted_token(quote)
            }
            _ => self.parse_unquoted_token(),
        }
    }

    fn require_token(&mut self, what: &str) -> Result<&'a str> {
        self.parse_token()
            .with_context(|| format!("expected `{what}` token"))
    }

    fn parse_quoted_token(&mut self, _quote: char) -> Option<&'a str> {
        None
    }

    fn parse_unquoted_token(&mut self) -> Option<&'a str> {
        let (token, rest) = self.s.split_once(' ')?;
        self.s = rest;
        Some(token)
    }

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
                    result: op!("result"),
                }
            };
        }
        macro_rules! binary {
            ($name:ident) => {
                Op::$name {
                    lhs: op!("lhs"),
                    rhs: op!("rhs"),
                    result: op!("result"),
                }
            };
        }

        let op = match name {
            "abs" => unary!(Abs),
            "add" => binary!(Add),
            "apply" => unary!(Apply),
            "canonical" => unary!(Canonical),
            "compare" => binary!(Compare),
            "comparesig" => binary!(CompareSig),
            "comparetotal" => binary!(CompareTotal),
            "copy" => unary!(Copy),
            "copyabs" => unary!(CopyAbs),
            "copynegate" => unary!(CopyNegate),
            "copysign" => binary!(CopySign),
            "max" => binary!(Max),
            "min" => binary!(Min),
            "multiply" => binary!(Multiply),
            "quantize" => binary!(Quantize),
            "subtract" => binary!(Subtract),
            "tointegralx" => unary!(ToIntegralX),
            _ => bail!("unknown op: `{name}`"),
        };
        Ok(op)
    }
}

enum Line<'a> {
    Test(Test<'a>),
    Directive(Directive<'a>),
}

enum Directive<'a> {
    Clamp(bool),
    Extended(bool),
    MaxExponent(i32),
    MinExponent(i32),
    Precision(i32),
    Rounding(RoundingMode),
    Version(&'a str),
}
