use crate::numbersystem::Number;
use crate::term::{Environment, Operator, PTerm, Term, Text, TextType};
use crate::pharsers::{Parsable, ParseResult, alt, char, item, item_satisfies, many, map, ignore_result, nat, obligatory_space, line_space, operator, optional, some, space, sym, this_string, token, within};
use crate::{numbersystem::Unit, pharsers::{Info, ShallowParser, Span}};
use crate::syntax_constants::{LINE_COMMENT, EVALUATE, ASSIGNMENT};
// In this module, the language specific parsers are defined, to generate Terms etc.

/// returns a string of digits, ignoring separators
/// 
/// # Examples
/// ```
/// let to_parse = Parsable::with_string("123'456 6554 is a number");
/// (result, tail) = separated_digits(to_parse).unwrap();
/// assert_eq!(result, 1235466554);
/// assert_eq!(tail, " is a number"); 
/// ```
/// according to [this](https://en.wikipedia.org/wiki/Decimal_separator) wikipedia entry (under Examples of use) the ' separator is only used in Switzerland, Liechtenstein and Italy
/// but whatever.
fn separated_digits<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, String> {
    // after nat suceeds, this parser will always suceed, because for example 1 counts as a separated digit.
    // (separators are ignored, not required)
    let (a, to_parse) = nat(to_parse)?; // ? ok because to_parse not yet modified
    let shallow_parser = ShallowParser::new(&to_parse);
    let res = 'inner: {
        // zero or less grouping symbols (valid grouping symbols are space and '), ? ok because many can't fail
        let (_, to_parse) = many(to_parse,|x|alt(x, vec![&|x|char(x,' '), &|x|char(x,'\'')]))?;
        
        let digits_res = separated_digits(to_parse);
        let Ok((b, to_parse)) = digits_res else {break 'inner Err(digits_res.err().unwrap())};
        Ok((format!("{}{}", a, b), to_parse))
    };
    match res {
        ok @ Ok(_) => ok,
        Err((to_parse, _)) => {
            let to_parse = to_parse.restore(shallow_parser);
            return Ok((format!("{a}"), to_parse))
        },
    }
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
fn fin_rational<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, (bool, i64, i64)> {
    fn fin_rational_inner<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, (bool, i64, i64)> {
        let (is_negative, to_parse) = optional(to_parse, |x|char(x, '-'), |x, _|Ok((true, x)), false)?;
        // parse digits, which may be separated by a space or a apostrophe (')
        let original_parsable = ShallowParser::new(&to_parse);
        let (number_string, to_parse) = separated_digits(to_parse)?;
        // convert a numberstring into an actual number
        let left = match number_string.parse::<i64>() {
            Ok(number) => number,
            Err(convert_msg) => {
                let info = Info {msg: format!("Failed to pharse number made of numbers (probably too big). 
                \n The error when converting to a number was: {}", convert_msg.to_string()),
                pos: Span{ start: original_parsable.span.start, end: to_parse.span.end }};
                return Err((to_parse.restore(original_parsable), info))
            }
        };

        let (number_string, to_parse) = optional(to_parse, |x|alt(x, vec![&|x|char(x,'.'), &|x|char(x,',')]), |x,_|separated_digits(x), "0".to_string())?;
        let right = match number_string.parse::<i64>() {
            Ok(number) => number,
            Err(convert_msg) => {
                let info = Info {msg: format!("Failed to pharse number made of numbers (probably too big). 
                \n The error when converting to a number was: {}", convert_msg.to_string()),
                pos: Span{ start: original_parsable.span.start, end: to_parse.span.end }};
                return Err((to_parse.restore(original_parsable), info))
            }
        };
        Ok(((is_negative, left, right), to_parse))
    }

    let shallow_parser = ShallowParser::new(&to_parse); 
    let res = fin_rational_inner(to_parse);
    match res {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            let to_parse = to_parse.restore(shallow_parser);
            return Err((to_parse,info))
        },
    }
}
/// parse exponential notation, as used often in calculators
/// 
/// This parses the part AFTER the number
/// 
/// `
/// 123 e12 kg -> e12 gets parsed. The optional space after the number gets handled by the number parser
fn e_notation<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, (bool, i64, i64)> {
    let shallow_parser = ShallowParser::new(&to_parse);
    // parse optional space before e notation
    let (_, to_parse) = line_space(to_parse)?; // can't fail, ? ok.
    let (_, to_parse) = match alt(to_parse, vec![&|x|char(x, 'e'), &|x|char(x, 'E')]) {
        Ok(res) => res,
        Err((to_parse, info)) => { // Note: some more convenient way to get the unexpected character would be nice
            // rebuild the parsable, to avoid cloning the whole information vectors.
            let next_item = to_parse.get_next_char();
            let info = Info {msg: format!("expected either e or E, found {}", next_item), pos: info.pos};
            return Err((to_parse.restore(shallow_parser), info))
        }
    };
    match fin_rational(to_parse) {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            // restore parsable to still contain e
            let to_parse = to_parse.restore(shallow_parser);
            let next_item = to_parse.get_next_char();
            let info = Info {msg: format!("expected number after e notation. found {}", next_item), pos: info.pos};
            return Err((to_parse, info))
        },
    }
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
fn number<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, PTerm> {
    let shallow_parser = ShallowParser::new(&to_parse);
    let res = 'inner: {
        let (_, to_parse) = space(to_parse)?; // space can't fail
        let number_star_pos = to_parse.span.start;
        let num_res = fin_rational(to_parse);
        let Ok((base,  to_parse)) = num_res else {break 'inner Err(num_res.err().unwrap())};

        // parsing of exponent notation
        // the sucess_fn argument here is the identity function, because everything is handled in the e_notation parser.
        // optional parser can't fail
        let (exponent, to_parse) = optional(to_parse, e_notation, |a, b|Ok((b, a)), (false, 0, 0))?;
        let number_end_pos = to_parse.span.start;
        //println!("base: {:?}, exponent: {:?}", base, exponent);
        // this is temporary, until I rework how values are stored (don't really fancy using floats)
        let value = {
            let comma_digits:u32 = (base.2).to_string().len() as u32;
            let divisor = (i32::pow(10, comma_digits)) as f64;
            //println!("base.1 as f: {}, base.2 as f: {}, divisor: {}", base.1 as f64, base.2 as f64, divisor);
            let base_value = (base.1 as f64 + (base.2 as f64)/divisor) * if base.0 {-1.0} else {1.0};
            
            let exp_comma_digits:u32 = (exponent.2).to_string().len() as u32;
            let exp_divisor = (i32::pow(10, exp_comma_digits)) as f64;
            let exponent_value = (exponent.1 as f64 + (exponent.2 as f64)/exp_divisor) * if exponent.0 {-1.0} else {1.0};
            //println!("base_value: {}, exponent_value: {}", base_value, exponent_value);
            base_value * f64::powf(10.0, exponent_value)
        };
        // convert the collected information into the numbersystem::Number type.
        let term = Term::Num(Number {
            value: value,
            unit: Unit::unitless(), // TODO: parse unit
        });
        let p_term = PTerm::new(term, Span{ start: number_star_pos, end: number_end_pos });
        Ok((p_term, to_parse))
    };
    match res {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            let to_parse = to_parse.restore(shallow_parser);
            return Err((to_parse,info))
        },
    }
}

/// Comment from the beginning of the comment symbol to the end of the line
fn line_comment<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, Text> {
    let (_, to_parse) = token(to_parse, |x|this_string(x, LINE_COMMENT))?;
    let start_pos = to_parse.span.start - LINE_COMMENT.len();

    let (text_type, to_parse) = optional(to_parse, 
        obligatory_space, 
        |x,_|Ok((TextType::Normal, x)), TextType::StrikeThrough).expect("many parser should never be able to fail");
    let (_content, to_parse) = (many(to_parse, |x|item_satisfies(x, |c|c!= (0xA as char) ))).expect("many parser should never be able to fail");
    let output = Text { text_type: text_type, span: Span { start: start_pos, end: to_parse.span.start } };
    Ok((output, to_parse))
}

// language specific pharsing

pub fn parse_file<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ((), Parsable<'a>) {
    // let res = alt(to_parse, vec![
    //     &|x|parse_assignment(x, env_tracker.clone())
    // ]);
    let res = parse_assignment(to_parse, env_tracker)
        .or_else(|(x, e1)|parse_comment(x, env_tracker)
        .or_else(|(x, e2)|ignore_result(x, obligatory_space) // this makes sure that all trailing whitespaces are parsed
        .or_else(|(x, e3)|parse_to_evaluate(x, env_tracker) // this makes sure that all trailing whitespaces are parsed
        .or_else(
            |(x, e4)| {
                let info = Info { msg: format!("Unexpected pattern. Expected assignment, comment or trailing whitespace. \
                                            The errors of these parsers are the following:\n \
                                            assignment:\t{:?}\n \
                                            comment:\t{:?}\n \
                                            trailing whitespace:\t{:?}\n
                                            evaluation:\t{:?}\n
                                            ", e1, e2, e3, e4),
                                        pos: Span{start: x.span.start, end: x.span.start}
                                      };
                Err((x, info))
                }
            ))));

    match res {
        Ok((_, to_parse)) => parse_file(to_parse, env_tracker), //return parse_file(to_parse, env_tracker),
        Err((to_parse, info)) => {
            if to_parse.span.start != to_parse.span.end {
                // TODO: get the most relevant parse error of the failed parsers
                // add that error with add_error
                // continue parsing on the next newline.
                let start = to_parse.span.start;
                let (consumed, mut to_parse) = many(to_parse, |x|item_satisfies(x, |c| c != (0xA as char))).ok().unwrap();
                let end = to_parse.span.start;
                let info = Info { msg: format!("Due to unexpected pattern: Skipped parsing of '{}'. continuing parsing after next new line (if any)\n \
                                                      More details: {:?}", consumed.trim_end(), info),
                        pos: Span{ start:start, end: end}
                    };
                to_parse = to_parse.add_error(info);
                parse_file(to_parse, env_tracker)
            } else {
                ((), to_parse)
            }
        }
        //Err((to_parse, _)) => ((), to_parse.restore(shallow_parser)),
    }
}

fn parse_comment<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()>{
    let (text, to_parse) = line_comment(to_parse)?;

    env_tracker.insert_text(text);
    Ok(((),to_parse))
}

/// parse variable assignments like a = 1+1 or b = a
/// Doesn't return content in the ParseResult but adds the assingment to the env_tracker argument
pub fn parse_assignment<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    let shallow_parser = ShallowParser::new(&to_parse);
    
    let res: ParseResult<'a, ()> = 'inner: {
        let var_start_pos = to_parse.span.start;
        // This two liner simulates a question mark returning from this scope.
        // For now i _think_ this is cleaner than using a match statement.
        // Note: I can't use ? because to_parse needs to be reset before exiting the function.
        // here the funky Err(x.err().unwrap()) has to be done, because the compiler doesn't know that result is an error,
        // and would consider it the wrong type
        // Maybe there could be a macro for this.
        let var_result = token(to_parse, sym);
        let Ok((var, to_parse)) = var_result else {break 'inner Err(var_result.err().unwrap())};

        let var_end_pos = to_parse.span.start;
        
        let eq_result = token(to_parse, |x|this_string(x, ASSIGNMENT));
        let Ok((_, to_parse)) = eq_result else {break 'inner Err(eq_result.err().unwrap())};

        let expr_result = parse_expression(to_parse);
        let Ok((expression, to_parse)) = expr_result else {break 'inner Err(expr_result.err().unwrap())};

        // at this point in the function we start modifying the env_tracker.
        // we can't return an error after this point, because that would leave the env_tracker in a bad state.
        let exists = env_tracker.insert_variable(var.clone(), expression);
        let to_parse = match exists {
            Some(overwritten) => to_parse.add_error(Info {
                // Note: maybe it is possible to report the position of the previous term (but for that I need to have the whole file string)
                msg: format!("'{}' already exists as '{}' in this scope. The previous definition will not be used. (scopes aren't implemented yet, if it was in another scope, this would merely be a warning)", var, overwritten.content),
                pos: Span{start: var_start_pos, end: var_end_pos},
            }),
            None => to_parse,
        };
        Ok(((), to_parse))
    };
    
    match res {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            let to_parse = to_parse.restore(shallow_parser);
            return Err((to_parse,info))
        },
    }
}

pub fn parse_to_evaluate<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    let shallow_parser = ShallowParser::new(&to_parse);
    let res: ParseResult<'a, ()> = 'inner: {
        let expr_result = parse_expression(to_parse);
        let Ok((term, to_parse)) = expr_result else {break 'inner Err(expr_result.err().unwrap())};
        
        let pat_result = parse_evaluation_pattern(to_parse);
        let Ok((_, to_parse)) = pat_result else {break 'inner Err(pat_result.err().unwrap())};
        
        env_tracker.insert_to_evaluate(term);
        Ok(((), to_parse))
    };
    match res {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            let to_parse = to_parse.restore(shallow_parser);
            return Err((to_parse, info))
        },
    }
}

/// parses = {}
/// it will eventually output some type telling how the result should be formattet.
pub fn parse_evaluation_pattern<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, ()> {
    let shallow_parser = ShallowParser::new(&to_parse);
    let res: ParseResult<'a, ()> = 'inner: {
        let eq_result = token(to_parse, |x|this_string(x, EVALUATE));
        let Ok((_, to_parse)) = eq_result else {break 'inner Err(eq_result.err().unwrap())};
        let (_, to_parse) = space(to_parse)?; // ? ok because space is unfailable
        // this will have to be broken up, to detect desired units and precision / e-notation etc
        let pat_result = this_string(to_parse, "{}");
        let Ok((_, to_parse)) = pat_result else {break 'inner Err(pat_result.err().unwrap())};
        Ok(((), to_parse))
    };
    match res {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            let to_parse = to_parse.restore(shallow_parser);
            return Err((to_parse,info))
        },
    }
}

/// Note: this parser deletes spaces when it fails. TODO: fix.
/// Questionmakrs should only be placed after unfailable parsers like space and many.
fn parse_expression<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, PTerm> {
    let shallow_parser = ShallowParser::new(&to_parse);
    let res: ParseResult<'a, PTerm> = 'inner: {
        let (_, to_parse) = space(to_parse)?;
        // TODO: put this into a function, because this code is used twice
        let first_res = alt(to_parse, vec![
        &number,
        &parse_variable, // note: I can't know if the parsed sym was defined. That must be handled in the evaluation stage.
        &parse_function, // when implemented, this (probably) has to happen before symbol parsing
        &|x|within(x, |x|char(x, '('), parse_expression, |x|char(x, ')')) // nesting is free.
        // TODO: parse single operator function and stuff like sqrt_3(5)
        ]);
        let Ok((first, to_parse)) = first_res else {break 'inner Err(first_res.err().unwrap())};
        break 'inner parse_expression_prime(to_parse, first);
    };
    let out = match res {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            let to_parse = to_parse.restore(shallow_parser);
            Err((to_parse,info))
        },
    };
    return out; // return needed, because the helper functions are defined after this.

    fn parse_expression_prime<'a>(to_parse: Parsable<'a>, first: PTerm) -> ParseResult<'a, PTerm> {
    let shallow_parser = ShallowParser::new(&to_parse);
    let res = 'inner: {
        // get the next operator, to be able to assemble right and left term
        let shallow_parser = ShallowParser::new(&to_parse);
        let (op1, to_parse) = match token(to_parse, parse_infix_op){
            Ok(ok) => ok,
            Err((to_parse, _)) => break 'inner Ok((first, to_parse)), // if there is no operator, we reached the end of the expression
        };
        let rhs_result = parse_expression_rhs(to_parse.restore(shallow_parser));
        let Ok((second, to_parse)) = rhs_result else {break 'inner Err(rhs_result.err().unwrap())};
        
        let span_start = first.span.start;
        let span_end = second.span.end;
        let recursive_first = PTerm::new(Term::DuOp(Box::new(first), op1, Box::new(second)),
            Span{ start: span_start, end: span_end });
        parse_expression_prime(to_parse, recursive_first)
    };
    match res {
        ok @ Ok(_) => ok,
        Err((to_parse, info)) => {
            let to_parse = to_parse.restore(shallow_parser);
            return Err((to_parse,info))
        },
    }
}

    /// gets the left hand side, given a string containing op1 num op2 num ...
    /// This could be num or num op2 num..., depending on the precedence and associativity of op1 and op2.
    fn parse_expression_rhs<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, PTerm> {
        let shallow_parser = ShallowParser::new(&to_parse);
        let res = 'inner: {
            // to parse contains _ op1 n2 op2 n3 ...
            // note that this parser MUST suceed (for now), because it was already applied sucessfully with the same inputin parse_expression_prime
            // we just apply it again, to get the first operator.
            let (op1, to_parse) = token(to_parse, parse_infix_op)?;
            let (_, to_parse) = space(to_parse)?;
            // to parse contains _ _ n2 op2 n3 ...
            let second_res = alt(to_parse, vec![
                &number,
                &parse_variable, // note: I can't know if the parsed sym was defined. That must be handled in the evaluation stage.
                &parse_function,
                &|x|within(x, |x|char(x, '('), parse_expression, |x|char(x, ')')) // nesting is free.
                ]); // if this parser fails, the expession ends with a operator which is invalid.
            let Ok((second, to_parse)) = second_res else {break 'inner Err(second_res.err().unwrap())};

            // to parse contains _ _ _ op2 n3 ...
            let shallow_parser = ShallowParser::new(&to_parse);
            match token(to_parse, parse_infix_op) {
                Ok((op2, modified_to_parse)) => {
                    // check if op1 or op2 have higher precedence
                    // if they are equal, check their associativity
                    if check_left_associative(&op1, &op2) {
                        Ok((second, modified_to_parse.restore(shallow_parser))) // return the right hand side belonging to op1. The rest of the equation gets handled by parse_expression_prime
                    } else {
                        // the next operator might be of even higher precedence.
                        // ex. 5+4*3^2
                        // at this point, the expression is parsed to _ op1(+) second * 3^2
                        // (notice how we don't update to_parse, when parsing op2)
                        // here, parse expression should output 3^2, as that's the left hand side of op2.
                        let third_res = parse_expression_rhs(modified_to_parse.restore(shallow_parser));
                        let Ok((third, to_parse)) = third_res else {break 'inner Err(third_res.err().unwrap())};
                        let span_start = second.span.start;
                        let span_end = third.span.end;
                        let term = Term::DuOp(Box::new(second), op2, Box::new(third));
                        Ok((PTerm::new(term, Span{ start: span_start, end: span_end } ), to_parse))
                    }
                },
                Err((to_parse, _)) => {
                    // op2 doesn't exist -> end of equation
                    Ok((second, to_parse))
                    //Ok((Term::DuOp(Box::new(first), op1, Box::new(second)), to_parse))
                },
            }
        };
        match res {
            ok @ Ok(_) => ok,
            Err((to_parse, info)) => {
                let to_parse = to_parse.restore(shallow_parser);
                return Err((to_parse,info))
            },
        }
    }
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

fn parse_variable<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, PTerm> {
    let var_start = to_parse.span.start;
    let (var, to_parse) = map(to_parse, sym, |sym|Term::Var(sym))?;
    Ok((PTerm::new(var, Span { start: var_start, end: to_parse.span.start }), to_parse))
}
fn parse_infix_op<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, Operator> {
    map( to_parse, operator, |op|Operator::Infix(op))
}
fn parse_function<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, PTerm> {
    // parse symbol (function name), parse opening paranthesis, parse the arguments inside the paranthesis with parse expression.
    // the arguments are delimited with "," (probably. This is another reason to not use commas as a thousands sign)
    
    let info = Info{
        msg: "Function parsing is not yet implemented. This parse error happened, because the input might be a function.".to_string(),
        pos: Span { start:to_parse.span.start, end: to_parse.span.start+1 }
    };
    Err((to_parse, info))
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_separated_digits() {
        let to_parse = Parsable::with_string("5 e10");
        let left = separated_digits(to_parse);
        assert_eq!(left, Ok(("5".to_string(), Parsable::with_str_offset(" e10", 1))));
    }
    #[test]
    fn test_fin_rational() {
        let to_parse = Parsable::with_string("-123'456.5 e-3");
        let left = fin_rational(to_parse);
        assert_eq!(left, Ok(((true, 123456, 5), Parsable::with_str_offset(" e-3",10))));
    }
    #[test]
    fn test_number() {
        let to_parse = Parsable::with_string("-123'456.5 something");
        let left = number(to_parse);

        let term = Term::Num(Number {
            value: -123456.5,
            unit: Unit::unitless(), // TODO: parse unit
        });
        let expected_result = Ok((PTerm::new(term, Span { start: 0, end: 10 } ),
            Parsable::with_str_offset(" something", 10)));
        assert_eq!(left, expected_result);
    }
    #[test]
    fn test_number_eq() {
        let to_parse = Parsable::with_string("7.3 = {}");
        let left = number(to_parse);

        let term = Term::Num(Number {
            value: 7.3,
            unit: Unit::unitless(), // TODO: parse unit
        });
        let expected_result = Ok((PTerm::new(term, Span { start: 0, end: 3 } ),
            Parsable::with_str_offset(" = {}", 3)));
        assert_eq!(left, expected_result);
    }
    #[test]
    fn test_number_e() {
        let to_parse = Parsable::with_string("-123'456.5 e-3");
        let left = number(to_parse);

        let term = Term::Num(Number {
            value: -123.4565,
            unit: Unit::unitless(), // TODO: parse unit
        });
        let expected_result = Ok((PTerm::new(term, Span { start: 0, end: 14 } ),
            Parsable::with_str_offset("", 14)));
        assert_eq!(left, expected_result);
    }
    #[test]
    fn newline_parsing() {
        let file_path = "testfile.tc";
        println!("pattern: {:?}", file_path);
        let contents = std::fs::read_to_string(file_path)
            .expect("Should have been able to read the file");
        for char in contents.chars() {
            if char == 0xA as char {
                println!("got a newline character");
                continue;
            }
            print!("<{}>", char.escape_unicode());
        }
    }
    #[test]
    fn test_parse_expression_number () {
        let to_parse = Parsable::with_string("7.3 = {}");
        let result = parse_expression(to_parse);

        let after_parse = Parsable::with_str_offset(" = {}", 3);
        
        let seven = Number { value: 7.3, unit: Unit::unitless() };
        let expected_term = PTerm::new(Term::Num(seven.clone()), Span::new(0,3));

        let right = Ok((expected_term, after_parse));
        assert_eq!(result, right);
    }
    #[test]
    fn test_parse_expression_no_space () {
        let to_parse = Parsable::with_string("7+7 = {}");
        let result = parse_expression(to_parse);

        let after_parse = Parsable::with_str_offset(" = {}", 3);
        
        let seven = Number { value: 7.0, unit: Unit::unitless() };
        let expected_term = PTerm::new(Term::DuOp(Box::new(PTerm::new(Term::Num(seven.clone()), Span::new(0,1))),
                                             Operator::Infix("+".to_string()),
                                             Box::new(PTerm::new(Term::Num(seven), Span::new(2,3)))),
                                             Span::new(0, 3));

        let right = Ok((expected_term, after_parse));
        assert_eq!(result, right);
    }
    #[test]
    fn test_parse_expression_space () {
        let to_parse = Parsable::with_string("7 + 7 = {}");
        let result = parse_expression(to_parse);

        let after_parse = Parsable::with_str_offset(" = {}", 5);
        
        let seven = Number { value: 7.0, unit: Unit::unitless() };
        let expected_term = PTerm::new(Term::DuOp(Box::new(PTerm::new(Term::Num(seven.clone()), Span::new(0,1))),
                                             Operator::Infix("+".to_string()),
                                             Box::new(PTerm::new(Term::Num(seven), Span::new(4,5)))),
                                             Span::new(0, 5));

        let right = Ok((expected_term, after_parse));
        assert_eq!(result, right);
    }
    #[test]
    fn test_parse_to_evaluate_expression () {
        let to_parse = Parsable::with_string("7*7 = {}");
        let mut env_tracker = Environment::new();
        let result = parse_to_evaluate(to_parse, &mut env_tracker);

        let after_parse = Parsable::with_str_offset("", 8);
        let right = Ok(((), after_parse));
        assert_eq!(result, right);
        let mut expected_environment = Environment::new();
        let seven = Number { value: 7.0, unit: Unit::unitless() };
        let expected_term = PTerm::new(Term::DuOp(Box::new(PTerm::new(Term::Num(seven.clone()), Span::new(0,1))),
                                             Operator::Infix("*".to_string()),
                                             Box::new(PTerm::new(Term::Num(seven), Span::new(2,3)))),
                                             Span::new(0, 3));
        expected_environment.insert_to_evaluate(expected_term);
        assert_eq!(env_tracker, expected_environment);
    }
}