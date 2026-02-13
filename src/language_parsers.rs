use std::collections::HashMap;

use crate::numbersystem::{Number, Quantity};
use crate::term::{Environment, Operator, PTerm, Term, Text, TextType};
use crate::pharsers::{Parsable, ParseResult, Spanned, alt, char, ignore_result, item, item_satisfies, line_space, many, map, nat, obligatory_space, operator, optional, some, space, sym, this_string, token, until, within};
use crate::{numbersystem::Unit, pharsers::{Info, ShallowParser, Span}};
use crate::syntax_constants::{ASSIGNMENT, EVALUATE, LINE_COMMENT, QUANTITY_DEF_KEYWORD, UNIT_DEF_KEYWORD};
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
/// 
/// The lenght of the number is limited by the datatype it is stored as. An i64, makes the max number of digits for naturals 19
/// The theoretical maximum number of digits is 2*19 = 28, excluding the dot, if the dot is in the middle of the number.
/// ^^^^^^^-- TODO: Update once the return type of this function is stable.
/// returns a tuple containing the sign (true if negative) rhs of the dot and the lhs of the dot, and the offset of the lhs.
/// 5.6 -> (false, 5, 6)
/// -3.1 -> (true, 3, 1)
/// 0.011 -> (false, 0, 3) (the offset information is otherwise lost because 001 as an int is 1)
/// Note: i considered having the first number be negative, if the sign is negative, but that won't work for -0.5 (for zero)
fn fin_rational<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, (bool, usize, usize, usize)> {
    fn fin_rational_inner<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, (bool, usize, usize, usize)> {
        let (is_negative, to_parse) = optional(to_parse, |x|char(x, '-'), |x, _|Ok((true, x)), false)?;
        // parse digits, which may be separated by a space or a apostrophe (')
        let original_parsable = ShallowParser::new(&to_parse);
        let (number_string, to_parse) = separated_digits(to_parse)?;
        // convert a numberstring into an actual number
        let left = match number_string.parse::<usize>() {
            Ok(number) => number,
            Err(convert_msg) => {
                let info = Info {msg: format!("Failed to pharse number made of numbers (probably too big). 
                \n The error when converting to a number was: {}", convert_msg.to_string()),
                pos: Span{ start: original_parsable.span.start, end: to_parse.span.end }};
                return Err((to_parse.restore(original_parsable), info))
            }
        };

        let (number_string, to_parse) = optional(to_parse, |x|alt(x, vec![&|x|char(x,'.'), &|x|char(x,',')]), |x,_|separated_digits(x), "0".to_string())?;
        let offset = number_string.len();
        let right = match number_string.parse::<usize>() {
            Ok(number) => number,
            Err(convert_msg) => {
                let info = Info {msg: format!("Failed to pharse number made of numbers (probably too big). 
                \n The error when converting to a number was: {}", convert_msg.to_string()),
                pos: Span{ start: original_parsable.span.start, end: to_parse.span.end }};
                return Err((to_parse.restore(original_parsable), info))
            }
        };
        Ok(((is_negative, left, right, offset), to_parse))
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
fn e_notation<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, (bool, usize, usize, usize)> {
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
        let (exponent, to_parse) = optional(to_parse, e_notation, |a, b|Ok((b, a)), (false, 0, 0, 1))?;
        let number_end_pos = to_parse.span.start;
        //println!("base: {:?}, exponent: {:?}", base, exponent);
        // this is temporary, until I rework how values are stored (don't really fancy using floats)
        let value = {
            let comma_digits = base.3 as u32;
            let divisor = (usize::pow(10, comma_digits)) as f64;
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

fn parse_quantity_definition<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    // parses everything after Quantity Name: symbol
    // which is " = <expression>" and returns the expected quantity
    // if the expression can't be evaluated, this parser suceeds but adds an error info to the parsable.
    fn derived_quantity<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &Environment) -> ParseResult<'a, Quantity> {
        let shallow_parser = ShallowParser::new(&to_parse);
        let res = 'inner: {
            let eq_res = token(to_parse, |x|this_string(x, ASSIGNMENT));
            let Ok((_, to_parse)) = eq_res else {break 'inner Err(eq_res.err().unwrap())};

            let expr_res = parse_expression(to_parse);
            let Ok((term, to_parse)) = expr_res else {break 'inner Err(expr_res.err().unwrap())};

            // evaluate the term which defines the new quantity
            match term.evaluate_quantity(&env_tracker) {
                Ok(quantity) => {
                    Ok((quantity, to_parse))
                },
                Err(info_vec) => {
                    // when we reach this point, we want to give this error to the user.
                    let info = Info{ msg: format!("Could not evaluate expression in Quantity definition. Threating this definition as unitless. The returned information vector was: {:?}", info_vec),
                    pos: term.span };
                    let to_parse = to_parse.restore(shallow_parser);
                    let to_parse = to_parse.add_error(info);
                    //break 'inner Err((to_parse.restore(), info));
                    Ok((Unit::unitless().quantity, to_parse))
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

    let shallow_parser = ShallowParser::new(&to_parse);
    let res = 'inner: {
        let quantity_def_start_pos = to_parse.span.start;
        let keyword_res = this_string(to_parse, QUANTITY_DEF_KEYWORD);
        let Ok((_, to_parse)) = keyword_res else {break 'inner Err(keyword_res.err().unwrap())};
        let (_, to_parse) = space(to_parse).expect("space parser can't fail, but failed anyways");
        // parses the name, which is terminated by either : or newline (0xA).
        let (name, to_parse) = optional(to_parse,
            |x|until(x, |x|item_satisfies(x, |c|c == ':' || c == (0xA as char))),
            |x, (quantity_name, _separator)| Ok((Some(quantity_name), x)),
            None).expect("optional parser can't fail");

        let symbol_res = token(to_parse, sym);
        let Ok((symbol, to_parse)) = symbol_res else {break 'inner Err(symbol_res.err().unwrap())};
        
        // parse base quantitys for derived
        // Use the usual math parsing to parse the expression (like l^2 for area definition) This way the existing parsing can be used.
        
        let (base_quantity, to_parse) = optional(to_parse,
            |x|derived_quantity(x, env_tracker),
        |to_parse, quantity|Ok((quantity.base_quantity, to_parse)),
        HashMap::from([(symbol.clone(), (None, 1))])).expect("optional parser can't fail");
        let quantity_def_end_pos = to_parse.span.start;

        let quantity = Quantity::new_coded(name, symbol.to_owned(), base_quantity);
        let exists = env_tracker.insert_quantity(symbol.clone(), Spanned::new(quantity, quantity_def_start_pos, quantity_def_end_pos));
        let to_parse = match exists {
            Some(overwritten) => to_parse.add_error(Info {
                // Note: maybe it is possible to report the position of the previous term (but for that I need to have the whole file string)
                msg: format!("Quantity '{}' already exists as '{}'. The previous definition will not be used. (scopes aren't implemented yet, if it was in another scope, this would merely be a warning)", symbol, overwritten.get_content()),
                pos: Span{start: quantity_def_start_pos, end: quantity_def_end_pos},
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

fn parse_unit_definition<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    /// parses " ('quantity symbol')" from "Unit 'Name': ("quantity symbol") = 'expression'"
    /// and returns the quantity, with its position. The position can be used to give error information,
    /// if in "Unit Gramforce: gf (F) = 1/9.81*kg*m/s^2" The quantity of the rhs isn't F.
    fn quantity_indicator<'a, 'b> (to_parse: Parsable<'a>, env_tracker: &'b Environment) -> ParseResult<'a, Spanned<Quantity>> {
        let shallow_parser = ShallowParser::new(&to_parse);
        // ? ok because it is the first parser call in this function (to_parse not yet modified)
        // note: the position includes space before the braket, and the opening and closing braket.
        // That's totally okay, since this position only gets used as an error output (and not for formatting)
        let sym_start_pos = to_parse.span.start;
        let (sym, to_parse) = token(to_parse,
            &|x|within(x, |x|char(x, '('), sym, |x|char(x, ')')),)?;
        let sym_end_pos = to_parse.span.start; // -1 for closing braket
        // get the associated quantity of the symbol
        match env_tracker.get_quantity(&sym) {
            Some(sp_quantity) => Ok((sp_quantity, to_parse)),
            None => {
                let info = Info{
                    msg: format!("Couldn't find the definition for the quantity '{}'. Quantitys must be defined before they can be used.", sym),
                    pos: Span::new(sym_start_pos, sym_end_pos)
                };
                let to_parse = to_parse.restore(shallow_parser);
                return Err((to_parse, info))
            },
        }
    }
    // parses everything after Unit Name: symbol
    // which is " = <expression>" and returns the expected unit and its modifier
    // if the expression can't be evaluated, this parser suceeds but adds an error info to the parsable.
    fn derived_unit<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &Environment) -> ParseResult<'a, (f64, Unit)> {
        let shallow_parser = ShallowParser::new(&to_parse);
        let res = 'inner: {
            let eq_res = token(to_parse, |x|this_string(x, ASSIGNMENT));
            let Ok((_, to_parse)) = eq_res else {break 'inner Err(eq_res.err().unwrap())};

            let expr_res = parse_expression(to_parse);
            let Ok((term, to_parse)) = expr_res else {break 'inner Err(expr_res.err().unwrap())};

            println!("derived_unit function going to evaluate: {:?}", term);
            // evaluate the term which defines the new quantity
            match term.evaluate_unit(&env_tracker) {
                Ok((modifier, unit)) => {
                    println!("evaluated to modifier: {} and Unit: {:?}", modifier, unit);
                    Ok(((modifier, unit), to_parse))
                },
                Err(info_vec) => {
                    // when we reach this point, we want to give this error to the user.
                    let info = Info{ msg: format!("Could not evaluate expression in Unit definition. Threating this definition as unitless with factor one. (If you want to have a unitless unit, use '= 1') The returned information vector was: {:?}", info_vec),
                    pos: term.span };
                    //let to_parse = to_parse.restore(shallow_parser); // don't restore, the parsed part was correct
                    let to_parse = to_parse.add_error(info);
                    //break 'inner Err((to_parse.restore(), info));
                    Ok(((1.0, Unit::unitless()), to_parse))
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

    let shallow_parser = ShallowParser::new(&to_parse);
    let res = 'inner: {
        let unit_def_start_pos = to_parse.span.start;
        let keyword_res = this_string(to_parse, UNIT_DEF_KEYWORD);
        let Ok((_, to_parse)) = keyword_res else {break 'inner Err(keyword_res.err().unwrap())};
        let (_, to_parse) = space(to_parse).expect("space parser can't fail, but failed anyways");
        // parses the name, which is terminated by either : or newline (0xA).
        let (name, to_parse) = optional(to_parse,
            |x|until(x, |x|item_satisfies(x, |c|c == ':' || c == (0xA as char))),
            |x, (quantity_name, _separator)| Ok((Some(quantity_name), x)),
            None).expect("optional parser can't fail");

        let symbol_res = token(to_parse, sym);
        let Ok((symbol, to_parse)) = symbol_res else {break 'inner Err(symbol_res.err().unwrap())};
        
        // return an option because this (quantity indicator in brakets) is optional for derived units
        let (spanned_quantity_option, to_parse) = optional(to_parse,
            |x|quantity_indicator(x, env_tracker),
            |x, sp_quantity|Ok((Some(sp_quantity),x)),
            None)?; // optional can't fail
        
        // parse base units for derived
        // Use the usual math parsing to parse the expression (like m^2 for squaremeter definition) This way the existing parsing can be used.
        // TODO: If a base unit is created, (default argument of optional parser) check if a base unit of this quantity already exists in
        // the env_tracker and give a warning.
        let (unit, to_parse) = optional(to_parse,
            |x|derived_unit(x, env_tracker),
            |to_parse, (modifier, unit)| {
                // applies the name and symbol to the derived unit
                let unit = Unit::new_coded(name.clone(), symbol.clone(), unit.base_unit, modifier, unit.quantity);        
                Ok((Some(unit), to_parse))
            },
            None).expect("optional parser can't fail");
        let unit_def_end_pos = to_parse.span.start;

        // generate the unit based on base units or quantity
        let unit = match (unit, spanned_quantity_option) {
            (None, None) => {
                // either the unit must be given via Unit: name = unit_expression
                // or the quantity must be given by Unit: name (quantity)
                // if neither is given, Error.
                let info = Info{ msg: format!("Either a base quantity must be given via 'Unit: name (quantity)', \
                or the unit must be defined with an expression as in 'via Unit: name = unit_expression'"),
                pos: Span::new(unit_def_start_pos, unit_def_end_pos) };
                let to_parse = to_parse.add_error(info);
                //break 'inner Err((to_parse.restore(), info));
                return Ok(((), to_parse)); // don't return a parser error, because the Unit keyword and the unit name was sucessfully parsed.
            },
            (None, Some(spanned_quantity)) => {
                // create base unit if the unit is not derived
                Unit::new_base(name, symbol.clone(), spanned_quantity.get_content(), 1.0)
            },
            // derived unit case
            (Some(unit), None) => unit,
            // derived unit with quantity check case
            (Some(unit), Some(spanned_quantity)) => {
                if &unit.quantity != spanned_quantity.get_content() {
                    let info = Info{ msg: format!("Quantity of unit defining expression was {} which is not equal to the defined quantity {}", unit.quantity, spanned_quantity.get_content()),
                    pos: Span::new(unit_def_start_pos, unit_def_end_pos) };
                    let to_parse = to_parse.add_error(info);
                    //break 'inner Err((to_parse.restore(), info));
                    return Ok(((), to_parse));
                }
                // this keeps the name of the quantity attached to the unit.
                Unit::new_base(name, symbol.clone(), spanned_quantity.get_content(), unit.modifier)
            },
        };

        let exists = env_tracker.insert_unit(symbol.clone(), Spanned::new(unit, unit_def_start_pos, unit_def_end_pos));
        let to_parse = match exists {
            Some(overwritten) => to_parse.add_error(Info {
                // Note: maybe it is possible to report the position of the previous term (but for that I need to have the whole file string)
                msg: format!("Unit '{}' already exists as '{}'. The previous definition will not be used. (scopes aren't implemented yet, if it was in another scope, this would merely be a warning)", symbol, overwritten.get_content()),
                pos: Span{start: unit_def_start_pos, end: unit_def_end_pos},
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
        let Ok((evaluated_position, to_parse)) = pat_result else {break 'inner Err(pat_result.err().unwrap())};
        
        env_tracker.insert_to_evaluate(term, evaluated_position);
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
/// For now it just outputs the position of where the result should be placed.
pub fn parse_evaluation_pattern<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, Span> {
    let shallow_parser = ShallowParser::new(&to_parse);
    let res: ParseResult<'a, Span> = 'inner: {
        let eq_result = token(to_parse, |x|this_string(x, EVALUATE));
        let Ok((_, to_parse)) = eq_result else {break 'inner Err(eq_result.err().unwrap())};
        let (_, to_parse) = space(to_parse)?; // ? ok because space is unfailable
        // TODO: this will have to be broken up, to detect desired units and precision / e-notation etc
        let result_position = Span::new(to_parse.span.start + 1, to_parse.span.start + 1);
        let pat_result = this_string(to_parse, "{}");
        let Ok((_, to_parse)) = pat_result else {break 'inner Err(pat_result.err().unwrap())};
        Ok((result_position, to_parse))
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
    use std::default;

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
        assert_eq!(left, Ok(((true, 123456, 5, 1), Parsable::with_str_offset(" e-3",10))));
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
    fn test_number_zeros() {
        // testcase created because apparently number parsed 0.001 as 0.1
        let to_parse = Parsable::with_string("0.001");

        let left = number(to_parse);
        let term = Term::Num(Number {
            value: 0.001,
            unit: Unit::unitless(), // TODO: parse unit
        });
        let expected_result = Ok((PTerm::new(term, Span { start: 0, end: 5 } ),
        Parsable::with_str_offset("", 5)));
        assert_eq!(left, expected_result);
    }
    #[test]
    fn test_fin_rational_zeros() {
        let to_parse = Parsable::with_string("0.001");
        let left = fin_rational(to_parse);
        let right = Ok(((false, 0, 1, 3),
        Parsable::with_str_offset("", 5)));
        assert_eq!(left, right)
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
    // #[test]
    // fn newline_parsing() {
    //     let file_path = "testfile.tc";
    //     println!("pattern: {:?}", file_path);
    //     let contents = std::fs::read_to_string(file_path)
    //         .expect("Should have been able to read the file");
    //     for char in contents.chars() {
    //         if char == 0xA as char {
    //             println!("got a newline character");
    //             continue;
    //         }
    //         print!("<{}>", char.escape_unicode());
    //     }
    // }
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
        expected_environment.insert_to_evaluate(expected_term, Span::new(7, 7));
        assert_eq!(env_tracker, expected_environment);
    }
    #[test]
    fn test_parse_quantity_definition() {
        let to_parse = Parsable::with_string(
            "Quantity length: l\n\
            Quantity area: A = l*l");
        let mut env_tracker = Environment::new();
        let (_, parse_result) = parse_quantity_definition(to_parse, &mut env_tracker)
            .expect("Quantity definition parser should not fail for this input");
        let expected_quantity_l = Quantity::new("length", "l", Vec::default());
        let expected_s_quantity = Spanned::new(expected_quantity_l.clone(), 0, 18);
        let mut expected_environment = Environment::new();
        expected_environment.insert_quantity("l".to_owned(), expected_s_quantity);
        assert_eq!(env_tracker, expected_environment);
        let expected_parse_result = Parsable::with_str_offset("\nQuantity area: A = l*l", 18);
        assert_eq!(parse_result, expected_parse_result);
        
        let (_, to_parse) = space(parse_result).expect("space failed, even thought it shouldn't");

        let (_, parse_result) = parse_quantity_definition(to_parse, &mut env_tracker)
            .expect("Quantity definition parser should not fail for this input");
        let expected_quantity_a = Quantity::new("area", "A", vec![(expected_quantity_l, 2)]);
        let expected_s_quantity = Spanned::new(expected_quantity_a.clone(), 19, 41);
        expected_environment.insert_quantity("A".to_owned(), expected_s_quantity);
        assert_eq!(env_tracker, expected_environment);
    }
    #[test]
    fn test_parse_unit_definition() {
        let to_parse = Parsable::with_string(
            "Quantity length: l\n\
            Quantity area: A = l*l\n\
            Unit meter: m (l)\n \
            Unit millimeter: mm = 0.001 * m \n
            Unit squaremeter: sq (A) = m*m"
        );
        let mut env_tracker = Environment::new();
        // parse the two defined quantities
        
        let (_, to_parse) = parse_quantity_definition(to_parse, &mut env_tracker)
            .expect("Quantity definition parser should not fail for this input");
        let (_, to_parse) = space(to_parse).expect("space parser can't fail");
        
        let (_, to_parse) = parse_quantity_definition(to_parse, &mut env_tracker)
            .expect("Quantity definition parser should not fail for this input");
        let (_, to_parse) = space(to_parse).expect("space parser can't fail");
        // Here the quantity definition does not get testet. cloning the env_tracker at this point
        // avoids manually constructing the used quantities
        let mut expected_environment = env_tracker.clone();
        // parse Unit meter: m (l)
        let (_, to_parse) = parse_unit_definition(to_parse, &mut env_tracker)
            .expect("Unit definition parser should not fail for this input. Expected to parse 'Unit meter: m (l)'");
        let (_, to_parse) = space(to_parse).expect("space parser can't fail");

        //--- test environment
        let length = expected_environment.get_quantity("l").expect("length should be in the environment").get_content().clone();
        let expected_meter = Unit::new_test_base("meter", "m", &length, 1.0);
        let sp_expected_meter = Spanned::new(expected_meter.clone(), 42, 59);
        expected_environment.insert_unit("m".to_string(), sp_expected_meter);

        assert_eq!(env_tracker, expected_environment);

        // parse Unit millimeter: mm = 1/1000 m
        let (_, to_parse) = parse_unit_definition(to_parse, &mut env_tracker)
            .expect("Unit definition parser should not fail for this input");

        //--- test environment
        let expected_millimeter = Unit::new_coded(Some("millimeter".to_string()),
            "mm".to_owned(),
            HashMap::from([("m".to_owned(), (None, 1))]),
            0.001,
            Quantity::new_nameless(vec![(length, 1)]));
        let sp_expected_millimeter = Spanned::new(expected_millimeter, 61, 92);
        expected_environment.insert_unit("mm".to_string(), sp_expected_millimeter);
        println!("to_parse errors are: {:?}", to_parse.clone().get_info());
        assert_eq!(env_tracker, expected_environment);

        let (_, to_parse) = space(to_parse).expect("space parser can't fail");
        // parse Unit squaremeter: sq = m*m
        let (_, to_parse) = parse_unit_definition(to_parse, &mut env_tracker)
            .expect("Unit definition parser should not fail for this input");

        let area = expected_environment.get_quantity("a").expect("area should be in the environment").get_content().clone();
    }
}