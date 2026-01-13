mod numbersystem;
mod pharsers;

use std::{collections::HashMap, fmt::Display};

use numbersystem::Number;
use pharsers::{ParseResult, optional, alt, seq, some, many, map, space, sym, operator, token, char, nat, item};

use crate::numbersystem::Unit;


// language implementation!
// let's start by pharsing expressions
#[derive(PartialEq, Debug)]
enum Term {
    // DualOperators. Functions like + - * /, which take a right hand side and a left hand side.
    DuOp (
        Box<Term>,
        Operator,
        Box<Term>,
    ),
    // placeholder for a number
    Var(String),
    // number with value and unit
    Num(Number),
    // A empty set. The result of dividing by zero.
    Empty,
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::DuOp(term1, operator, term2) => {
                let op_sym = match operator {
                    Operator::Infix(sym) => {sym},
                    _ => "¿"
                };
                write!(f, "({}{}{})", term1, op_sym, term2)
            },
            Term::Var(sym) => write!(f, "{}", sym),
            Term::Num(number) => number.fmt(f),
            Term::Empty => write!(f, "{{}}"),
        }
    }
    //write!(f, "{} [{}]", {self.value}, {&self.unit})
}

// this isn't expandable at runtime.
#[derive(PartialEq, Debug)]
enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Infix(String)
}

type Environment = HashMap<String, Term>;

fn main() {
    //let file_path = std::env::args().nth(1).expect("no path given");
    let file_path = "testfile.tc";
    println!("pattern: {:?}", file_path);
    let contents = std::fs::read_to_string(file_path)
        .expect("Should have been able to read the file");
    println!("{}", contents);
    let mut env_tracker = HashMap::default();
    for line in contents.lines() {
        (env_tracker, _) = parse_assignment(line, env_tracker).expect("failed to parse");
    }

    // pretty print the environment
    for (key, value) in env_tracker {
        println!("variable name: {key}, \nvalue: {}", value);
    }
}

// below, a few language specific parsers are defined. I want to refactor them into their own file eventually

/// returns a string of digits, ignoring separators
/// 
/// # Examples
/// ```
/// let to_parse = "123'456 6554 is a number"
/// (result, tail) = separated_digits(to_parse).unwrap();
/// assert_eq!(result, 1235466554);
/// assert_eq!(tail, " is a number"); 
/// ```
/// according to [this](https://en.wikipedia.org/wiki/Decimal_separator) wikipedia entry (under Examples of use) the ' separator is only used in Switzerland, Liechtenstein and Italy
/// but whatever.
fn separated_digits<'a>(to_parse: &'a str) -> ParseResult<'a, String> {
    let (a, to_parse) = nat(to_parse)?;
    // zero or less grouping symbols (valid grouping symbols are space and ')
    let (_, to_parse) = many(to_parse,|x|alt(x, vec![&|x|char(x,' '), &|x|char(x,'\'')]))?;
    let (b, to_parse) = many(to_parse, separated_digits)?;
    Ok((format!("{}{}", a, b), to_parse))

    // consider returning a i64
}

// this function is language specific, because it defines that a number can be written with a , or a . as a separator.
// actually, this poses a problem, because in some countries ',' is used to separate thousands: 2,000.5 is what germans would call 2'000,5
// also, I want to use , as a function argument separator -> may only work if i use , followed by a space as a function argument separator, if the argument is a number.

/// Parses rational numbers with a finite representation (example 0.333... isn't parsed by this)
/// TODO: accept separators.
/// The length (number of digits) is capped by the nat parser.
/// As of writing this, the nat parser returns an i64, which makes the max number of digits for naturals 19
/// The theoretical maximum number of digits is 2*19 = 28, excluding the dot, if the dot is in the middle of the number.
/// ^^^^^^^-- TODO: Update once the return type of this function is stable.
/// returns a tuple containing the sign (true if negative) rhs of the dot and the lhs of the dot
/// 5.6 -> (false, 5, 6)
/// -3.1 -> (true, 3, 1)
/// Note: i considered having the first number be negative, if the sign is negative, but that won't work for -0.5 (for zero)
fn fin_rational<'a>(to_parse: &'a str) -> ParseResult<'a, (bool, i64, i64)> {
    let (is_negative, to_parse) = optional(to_parse, |x|char(x, '-'), |x, _|Ok((true, x)), false)?;
    // parse digits, which may be separated by a space or a apostrophe (')
    let (number_string, to_parse) = separated_digits(to_parse)?;
    // convert a numberstring into an actual number
    let left = match number_string.parse::<i64>() {
        Ok(number) => number,
        Err(msg) => return Err(format!("Failed to pharse number made of numbers (probably too big). \n The error when converting to a number was: {}", msg.to_string())),
    };

    let (number_string, to_parse) = optional(to_parse, |x|alt(x, vec![&|x|char(x,'.'), &|x|char(x,',')]), |x,_|separated_digits(x), "0".to_string())?;
    let right = match number_string.parse::<i64>() {
        Ok(number) => number,
        Err(msg) => return Err(format!("Failed to pharse number made of numbers (probably too big). \n The error when converting to a number was: {}", msg.to_string())),
    };
    Ok(((is_negative, left, right), to_parse))
}
/// parse exponential notation, as used often in calculators
/// 
/// This parses the part AFTER the number
/// 
/// `
/// 123 e12 kg -> space and e12 get parsed (space is optional)
fn e_notation<'a>(to_parse: &'a str) -> ParseResult<'a, (bool, i64, i64)> {
    let (_, to_parse) = space(to_parse)?; // can't fail
    let (_, to_parse) = match alt(to_parse, vec![&|x|char(x, 'e'), &|x|char(x, 'E')]) {
        Ok(res) => res,
        Err(_) => return Err(format!("expected either e or E, found {}", item(to_parse)?.0)), // this line will propagate the end of file error message, if item fails
    };
    fin_rational(to_parse)
}

/// parsers a number in the context of the language
/// The parser fails if the given number
/// a number in the language is:
/// a number followed by a unit, example: 5 kg
/// The number can also be written in scientific notation: 572.3 = 5.723 e2
/// for the scientific notation, multiple digits are allowed before the dot.
/// The space before the e may be omittet. The e may be upper or lowercase.
/// 5.723 * 10^2 will result in the same number (in the context of the language)
/// after the evaluation of the expression.
/// with xyz * 10^(abc), abc can be an expression. This doesn't work with e
/// If no unit is provided, the number is unitless 5 [-]
/// TODO: Complex numbers should be parsed by this too.
/// TODO: binary and hex representation would be cool.
fn number<'a>(to_parse: &'a str) -> ParseResult<'a, Term> {
    let (_, to_parse) = space(to_parse)?;
    let (base,  to_parse) = fin_rational(to_parse)?;

    // parsing of exponent notation
    // parse optional space before e notation
    let (_, to_parse) = space(to_parse)?;
    // the sucess_fn argument here is the identity function, because everything is handled in the e_notation parser.
    let (exponent, to_parse) = optional(to_parse, e_notation, |a, b|Ok((b, a)), (false, 0, 0))?;
    println!("base: {:?}, exponent: {:?}", base, exponent);
    // this is temporary, until I rework how values are stored (don't really fancy using floats)
    let value = {
        let divisor = ((base.2).to_string().len() * 10) as f64;
        let base_value = (base.1 as f64 + (base.2 as f64)/divisor) * if base.0 {-1.0} else {1.0};
        
        let exp_divisor = ((exponent.2).to_string().len() * 10) as f64;
        let exponent_value = (exponent.1 as f64 + (exponent.2 as f64)/exp_divisor) * if exponent.0 {-1.0} else {1.0};
        println!("base_value: {}, exponent_value: {}", base_value, exponent_value);
        base_value * f64::powf(10.0, exponent_value)
    };
    // convert the collected information into the numbersystem::Number type.
    let term = Term::Num(Number {
        value: value,
        unit: Unit::unitless(), // TODO: parse unit
    });

    Ok((term, to_parse))
}

// language specific pharsing
fn parse_assignment<'a, 'b>(to_parse: &'a str, mut env_tracker: Environment) -> ParseResult<'a, Environment> {
    let (var, to_parse) = token(to_parse, sym)?;
    let (_, to_parse) = token(to_parse, |x|char(x, '='))?;
    let (expression, to_parse) = parse_expression(to_parse)?;
    env_tracker.insert(var, expression); // TODO: At some point I want to give information, if a variable was overwritten. that probably extends the return type of this function
    Ok((env_tracker, to_parse))
}
fn parse_expression<'a>(to_parse: &'a str) -> ParseResult<'a, Term> {
    let (_, to_parse) = space(to_parse)?;
    let (first, to_parse) = alt(to_parse, vec![
    &number,
    &|x|map(x, sym, |sym|Term::Var(sym)), // note: I can't know if the parsed sym was defined. That must be handled in the evaluation stage.
    &parse_function,
    // TODO: parse single operator function and stuff like sqrt_3(5)
    ])?;

    fn parse_expression_prime<'a>(to_parse: &'a str, first: Term) -> ParseResult<'a, Term> {
        let (_, to_parse) = space(to_parse)?;
        // get the next operator, to be able to assemble right and left term
        let (op1, _) = match parse_infix_op(to_parse){
            Ok(ok) => ok,
            Err(_) => return Ok((first, to_parse)), // if there is no operator, we reached the end of the expression
        };
        let (second, to_parse) = parse_expression_rhs(to_parse)?;
        
        let recursive_first = Term::DuOp(Box::new(first), op1, Box::new(second));
        parse_expression_prime(to_parse, recursive_first)
    }

    /// gets the left hand side, given a string containing op1 num op2 num ...
    /// This could be num or num op2 num..., depending on the precedence and associativity of op1 and op2.
    fn parse_expression_rhs<'a>(to_parse: &'a str) -> ParseResult<'a, Term> {
        // to parse contains _ op1 n2 op2 n3 ...
        // note that this parser MUST suceed (for now), because it was already applied sucessfully with the same inputin parse_expression_prime
        // we just apply it again, to get the first operator.
        let (op1, to_parse) = parse_infix_op(to_parse)?;
        let (_, to_parse) = space(to_parse)?;
        // to parse contains _ _ n2 op2 n3 ...
        let (second, to_parse) = alt(to_parse, vec![
            &number,
            &|x|map(x, sym, |sym|Term::Var(sym)), // note: I can't know if the parsed sym was defined. That must be handled in the evaluation stage.
            &parse_function,
            ])?; // if this parser fails, the expession ends with a operator which is invalid.
        
        let (_, to_parse) = space(to_parse)?;
        // to parse contains _ _ _ op2 n3 ...
        match parse_infix_op(to_parse) {
            Ok((op2, _)) => {
                // check if op1 or op2 have higher precedence
                // if they are equal, check their associativity
                if check_left_associative(&op1, &op2) {
                    Ok((second, to_parse)) // return the right hand side belonging to op1. The rest of the equation gets handled by parse_expression_prime
                } else {
                    // the next operator might be of even higher precedence.
                    // ex. 5+4*3^2
                    // at this point, the expression is parsed to _ op1(+) second * 3^2
                    // (notice how we don't update to_parse, when parsing op2)
                    // here, parse expression should output 3^2, as that's the left hand side of op2.
                    let (third, to_parse) = parse_expression_rhs(to_parse)?;
                    let term = Term::DuOp(Box::new(second), op2, Box::new(third));
                    Ok((term, to_parse))
                }
            },
            Err(_) => {
                // op2 doesn't exist -> end of equation
                Ok((second, to_parse))
                //Ok((Term::DuOp(Box::new(first), op1, Box::new(second)), to_parse))
            },
        }
    }

    parse_expression_prime(to_parse, first)
}


/// currently totally hardcoded to only consider multiplication and division above everything else.
/// should give true if op1 has a higher precedence as op2 AND is left associative.
fn check_left_associative(op1:&Operator, op2:&Operator) -> bool {
    // until there is a way to define operators, the associativity is hardcoded in here
    // let operator_tracker = [
    //         [Operator::Infix("*".to_string()), Operator::Infix("/".to_string())], // todo: infix left
    //         [Operator::Infix("+".to_string()), Operator::Infix("-".to_string())] // also infix left
    //     ];
    // true if op1 has higher precedence as op2.
    // else (if the infix level of op1 and op2 is left), true
    // else false
    if *op1 == Operator::Infix("*".to_string()) || *op1 == Operator::Infix("/".to_string()) {
        true
    } else {
        false
    }
}

fn parse_infix_op<'a>(to_parse: &'a str) -> ParseResult<'a, Operator> {
    map( to_parse, operator, |op|Operator::Infix(op))
}
fn parse_function<'a>(to_parse: &'a str) -> ParseResult<'a, Term> {
    // parse symbol (function name), parse opening paranthesis, parse the arguments inside the paranthesis with parse expression.
    // the arguments are delimited with "," (probably. This is another reason to not use commas as a thousands sign)
    let _unused = to_parse;
    Err("Function parsing is not yet implemented. This parse error happened, because the input might be a function.".to_string())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_separated_digits() {
        let to_parse = "5e10";
        let left = separated_digits(to_parse);
        assert_eq!(left, Ok(("5".to_string(), "e10")));
    }
    #[test]
    fn test_fin_rational() {
        let to_parse = "-123'456.5 e-3";
        let left = fin_rational(to_parse);
        assert_eq!(left, Ok(((true, 123456, 5), "e-3")));
    }
    #[test]
    fn test_number() {
        let to_parse = "-123'456.5 e-3";
        let left = number(to_parse);

        let term = Term::Num(Number {
            value: -123.4565,
            unit: Unit::unitless(), // TODO: parse unit
        });
        assert_eq!(left, Ok((term, "")));
    }
}

