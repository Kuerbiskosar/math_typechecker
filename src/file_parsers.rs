// contains high level parsers which parse files and modify the environment
use std::collections::HashMap;

use crate::pharsers::{Parsable, ParseResult, Spanned, alt, char, ignore_result, item, item_satisfies, line_space, many, map, nat, obligatory_space, operator, optional, some, space, sym, this_string, token, until, within};
use crate::language_parsers::{parse_evaluation_pattern, parse_expression, line_comment};
use crate::numbersystem::{Number, Quantity};
use crate::term::{Environment, Operator, PTerm, Term, Text, TextType};
use crate::syntax_constants::{ASSIGNMENT, EVALUATE, LINE_COMMENT, QUANTITY_DEF_KEYWORD, UNIT_DEF_KEYWORD};
use crate::{numbersystem::Unit, pharsers::{Info, ShallowParser, Span}};

pub fn parse_file<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ((), Parsable<'a>) {
    // let res = alt(to_parse, vec![
    //     &|x|parse_assignment(x, env_tracker.clone())
    // ]);
    let res = parse_assignment_to_evaluate(to_parse, env_tracker)
        .or_else(|(x, e_assign_eval)|parse_assignment(x, env_tracker)
        .or_else(|(x, e_assignment)|parse_equation(x, env_tracker)
        .or_else(|(x, e_equation)|parse_comment(x, env_tracker)
        .or_else(|(x, e_comment)|parse_to_evaluate(x, env_tracker)
        .or_else(|(x, e_evaluate)|parse_quantity_definition(x, env_tracker)
        .or_else(|(x, e_quantity)|parse_unit_definition(x, env_tracker)
        .or_else(|(x, e_unit)|ignore_result(x, obligatory_space) // this makes sure that all trailing whitespaces are parsed
        .or_else(
            |(x, e_trailing_space)| {
                let info = Info { msg: format!("Unexpected pattern. Expected assignment, comment or trailing whitespace. \
                                            The errors of these parsers are the following:\n \
                                            assignment and evaluation: \t{e_assign_eval:?}\n \
                                            assignment:\t{e_assignment:?}\n \
                                            equation:\t{e_equation:?}\n \
                                            comment:\t{e_comment:?}\n \
                                            evaluation:\t{e_evaluate:?}\n
                                            quantity_definition:\t{e_quantity:?}\n
                                            unit_definition:\t{e_unit:?}\n
                                            trailing whitespace:\t{e_trailing_space:?}\n
                                            "),
                                        pos: Span{start: x.span.start, end: x.span.start}
                                      };
                Err((x, info))
                }
            )))))))); // one bracket for each parser in the .or_else chain, to keep errors in the scope of the last or_else.

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

        let expr_result = parse_expression(to_parse, &env_tracker);
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

fn parse_comment<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()>{
    let (text, to_parse) = line_comment(to_parse)?;

    env_tracker.insert_text(text);
    Ok(((),to_parse))
}


pub fn parse_to_evaluate<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    let shallow_parser = ShallowParser::new(&to_parse);
    let res: ParseResult<'a, ()> = 'inner: {
        let expr_result = parse_expression(to_parse, &env_tracker);
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

/// parses two or more terms connected with an equal sign.
/// This parser must be used after assignment parsing, because a single, not yet defined variable is an assignment.
/// MaybeTODO: change assignment function to fail if a variable gets "overwritten", because it might be an equation.
fn parse_equation<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    let shallow_parser = ShallowParser::new(&to_parse);
    
    let res: ParseResult<'a, ()> = 'inner: {
        let expr1_result = parse_expression(to_parse, &env_tracker);
        let Ok((expression1, to_parse)) = expr1_result else {break 'inner Err(expr1_result.err().unwrap())};
        
        let eq_result = token(to_parse, |x|this_string(x, ASSIGNMENT));
        let Ok((_, to_parse)) = eq_result else {break 'inner Err(eq_result.err().unwrap())};

        let expr2_result = parse_expression(to_parse, &env_tracker);
        let Ok((expression2, to_parse)) = expr2_result else {break 'inner Err(expr2_result.err().unwrap())};

        // a = b = c = d = e

        // at this point in the function we start modifying the env_tracker.
        // we can't return an error after this point, because that would leave the env_tracker in a bad state.

        env_tracker.insert_equation(expression1, expression2);
        // check for maybe more chained terms
        let mut to_parse = to_parse; // make to_parse modifiable, to update it in previous iterations of the loop
        let to_parse = loop {
            // let expression1 = expression2.clone(); // handled through insert_appended_equation method
            let shallow_parser = ShallowParser::new(&to_parse);
            let eq_result = token(to_parse, |x|this_string(x, ASSIGNMENT));
            let Ok((_, to_parse_loop)) = eq_result else {
                let to_parse = eq_result.err().unwrap().0.restore(shallow_parser);
                break to_parse;
            };

            let expr_result = parse_expression(to_parse_loop, &env_tracker);
            let Ok((expression2, to_parse_loop)) = expr_result else {
                let to_parse = expr_result.err().unwrap().0.restore(shallow_parser);
                break to_parse;
            };

            env_tracker.insert_appended_equation(expression2);
            to_parse = to_parse_loop;
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

/// parses something in the form of
/// sym = term = {evaluation_pattern}
fn parse_assignment_to_evaluate<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    let shallow_parser = ShallowParser::new(&to_parse);
    
    let res: ParseResult<'a, ()> = 'inner: {
        let var_start_pos = to_parse.span.start;
        let var_result = token(to_parse, sym);
        let Ok((var, to_parse)) = var_result else {break 'inner Err(var_result.err().unwrap())};

        let var_end_pos = to_parse.span.start;
        
        let eq_result = token(to_parse, |x|this_string(x, ASSIGNMENT));
        let Ok((_, to_parse)) = eq_result else {break 'inner Err(eq_result.err().unwrap())};

        let expr_result = parse_expression(to_parse, &env_tracker);
        let Ok((expression, to_parse)) = expr_result else {break 'inner Err(expr_result.err().unwrap())};

        let pat_result = parse_evaluation_pattern(to_parse);
        let Ok((evaluated_position, to_parse)) = pat_result else {break 'inner Err(pat_result.err().unwrap())};

        // at this point in the function we start modifying the env_tracker.
        // we can't return an error after this point, because that would leave the env_tracker in a bad state.
        let exists = env_tracker.insert_evaluated_variable(var.clone(), expression, evaluated_position);
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

/// parses something in the form of
/// sym = term = term = ... = {evaluation_pattern}
fn parse_assignment_eqation_evaluate<'a, 'b>(to_parse: Parsable<'a>, env_tracker: &'b mut Environment) -> ParseResult<'a, ()> {
    todo!()
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

            let expr_res = parse_expression(to_parse, &env_tracker);
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
    /// parses " ('quantity symbol')" from "Unit 'Name': 'unit symbol' ("quantity symbol") = 'expression'"
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

            let expr_res = parse_expression(to_parse, &env_tracker);
            let Ok((term, to_parse)) = expr_res else {break 'inner Err(expr_res.err().unwrap())};

            // evaluate the term which defines the new quantity
            match term.evaluate_unit(&env_tracker) {
                Ok((modifier, unit)) => {
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

        // TODO: I want to allow symbols like ° or ' as units.
        // TODO: check that this change doesn't interfere with operator parsing
        // (15m+7 should work, but '' should be a valid symbol (for degree seconds), therefore ++ could be either a operator or a unit symbol)
        // (since both need to be defined, before parsing the actual expression, we can throw an error if ++ is defined as both an operator and a unit smbol.)
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
                let unit = Unit::new_coded(name.clone(), Some(symbol.clone()), unit.base_unit, modifier, unit.quantity);
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


#[cfg(test)]
mod tests {
    use std::default;
    use crate::language_parsers::number;
    use super::*;
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
            Some("mm".to_owned()),
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

        let area = expected_environment.get_quantity("A").expect("area should be in the environment").get_content().clone();
    }
    #[test]
    fn test_unit_parsing_juxtaposed() {
        let mut env_tracker = Environment::new();
        let to_parse = Parsable::with_string("\
Quantity: l
Unit: m (l)
5 m + something...");
        let (_, to_parse) = parse_quantity_definition(to_parse, &mut env_tracker).expect("Should be able to parse Quantity: l");
        let (_, to_parse) = space(to_parse).expect("space shouldn't fail");
        let (_, to_parse) = parse_unit_definition(to_parse, &mut env_tracker).expect("Should be able to parse Unit: m (l)");
        let (_, to_parse) = space(to_parse).expect("space shouldn't fail");
        let num_result = number(to_parse, &env_tracker);
        let expected_unit = env_tracker.get_unit("m").expect("unit m should be in the environment").get_content().clone();
        let expected_number = PTerm::new(Term::Num(Number { value: 5.0, unit: expected_unit }), Span::new(24, 27));
        let expected_parsable = Parsable::with_str_offset(" + something...", 27);
        let expected_result = Ok((expected_number, expected_parsable));
        assert_eq!(num_result, expected_result);
    }
    #[test]
    fn test_unit_parsing_within() {
                let mut env_tracker = Environment::new();
        let to_parse = Parsable::with_string("\
Quantity: l
Quantity: t
Unit: m (l)
Unit: s (t)

5 [m/s*m] + something...");
        let (_, to_parse) = parse_quantity_definition(to_parse, &mut env_tracker).expect("Should be able to parse Quantity: l");
        let (_, to_parse) = space(to_parse).expect("space shouldn't fail");
        let (_, to_parse) = parse_quantity_definition(to_parse, &mut env_tracker).expect("Should be able to parse Quantity: t");
        let (_, to_parse) = space(to_parse).expect("space shouldn't fail");

        let (_, to_parse) = parse_unit_definition(to_parse, &mut env_tracker).expect("Should be able to parse Unit: m (l)");
        let (_, to_parse) = space(to_parse).expect("space shouldn't fail");
        let (_, to_parse) = parse_unit_definition(to_parse, &mut env_tracker).expect("Should be able to parse Unit: s (t)");
        let (_, to_parse) = space(to_parse).expect("space shouldn't fail");

        let num_result = number(to_parse, &env_tracker);
        let length = env_tracker.get_quantity("l").expect("l should exist").get_content().clone();
        let time = env_tracker.get_quantity("t").expect("t should exist").get_content().clone();

        let expected_quantity = Quantity { name: None, symbol: None, base_quantity: HashMap::from([("l".to_owned(), (None, 2)), ("t".to_owned(), (None, -1))]) };
        let expected_base_unit = HashMap::from([("s".to_owned(), (None, -1)), ("m".to_owned(), (None, 2))]);
        let expected_unit = Unit{ name: None, symbol: None, base_unit: expected_base_unit, quantity: expected_quantity, modifier: 1.0 };
        let expected_number = PTerm::new(Term::Num(Number { value: 5.0, unit: expected_unit }), Span::new(49, 58));
        let expected_parsable = Parsable::with_str_offset(" + something...", 58);
        let expected_result = Ok((expected_number, expected_parsable));
        assert_eq!(num_result, expected_result);
    }
}