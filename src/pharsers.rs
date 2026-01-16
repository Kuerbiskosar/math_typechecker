/*
    a pharser of things
  is a function from strings
     to lists of pairs
    Of things and strings
~ Graham Hutton
*/
// TODO: Parsers or Pharsers...? pretty shure it is the second one.
/// Output of pharsers. The pharser generates a output of Type T, based on some input &str.
/// The unprocessed part of the input gets returned as the second element of the returned tuple.
/// If the pharser doesn't succeed, an error result gets returned inside Err.
pub type ParseResult<'a,T> = Result<(T, &'a str), String>; // error messages must be strings, because they contain information which is not known at compile time (such as on which line the error ocurred)
//type Pharser2<'a, T> = dyn Fn(&str) -> ParseResult<'a, T>;
//type Pharser = &str -> Result<(char,int),&str>;
// gets one character from the string. basic building block for further pharsers
pub fn item<'a>(to_parse: &'a str) -> ParseResult<'a, char> {
    // condiser pharsing whole grapheme clusters, to interpret symbols build with stopchars and their "hardcoded" unicode equivalent the same
    fn strip_first_char(to_strip: &str) -> &str {
        let mut chars = to_strip.chars();
        chars.next();
        chars.as_str()
    }
    match to_parse.chars().nth(0) {
        Some(character) => Ok((character, strip_first_char(to_parse))),
        None => Err("unexpected end of input".to_string()),
    }
}
/// succeeds with the first character, if the character fulfills the predicate
fn item_satisfies<'a, Predicate>(to_parse: &'a str, predicate: Predicate) -> ParseResult<'a, char> 
where
    Predicate: Fn(char) -> bool
{
    let (token, remaining) = item(&to_parse)?;
    if predicate(token) {
        Ok((token, remaining))
    } else {
        Err(format!("character '{}' doesn't fulfill predicate", token))
    }
}

// single character pharsers

fn alphabetic<'a>(to_parse: &'a str) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x: char| x.is_alphabetic())
}
fn digit<'a>(to_parse: &'a str) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_digit(10)) // consider adding pharsers for other common bases
}
fn alphanumeric<'a>(to_parse: &'a str) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_alphanumeric())
}
fn valid_operator<'a>(to_parse: &'a str) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x: char|   !x.is_alphanumeric() &&
                                                    !x.is_whitespace() &&
                                                    !(x == '(') && !(x == ')'))
}

fn upper<'a>(to_parse: &'a str) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_uppercase())
}
fn lower<'a>(to_parse: &'a str) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_lowercase())
}
pub fn char<'a>(to_parse: &'a str, char_to_match: char) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x| x == char_to_match)
}

// applies the pharser at least once
pub fn some<'a, Parser, S>(to_parse: &'a str, parser: Parser) -> ParseResult<'a, String> 
where
   Parser: Fn(&'a str) -> ParseResult<'a, S>,
   S: ToString
   //Parser: Fn(&'a str) -> Result<(char, &'a str), &str>
{
    match parser(to_parse) {
        Ok((a, to_parse_tail)) => {
            match many(to_parse_tail, parser) {
                Ok((string, pharse_tail)) => Ok((format!("{}{}", a.to_string(), string), pharse_tail)),
                err @ Err(_) => err,
            }
        },
        Err(message) => Err(message)
    }
}
/// applies the pharser until it fails, returning the result as a string
/// The result of the pharser must be convertible to a string
pub fn many<'a, Parser, S>(to_parse: &'a str, parser: Parser) -> ParseResult<'a, String>
where
   Parser: Fn(&'a str) -> ParseResult<'a, S>,
   S: ToString
{
    match parser(to_parse) {
        Ok((a, to_parse_tail)) => {
            match some(to_parse_tail, parser) {
                Ok((string, pharse_tail)) => Ok((format!("{}{}", a.to_string(), string), pharse_tail)),
                Err(_) => Ok((a.to_string(), to_parse_tail)), // return with empty string
            }
        },
        Err(_) => Ok(("".to_string(), to_parse)),
    }
}

// this doesn't work. Once again, I was a fool to follow the advice of a large language model.
// usually functions which take tuples of "arbitrary" length are limited to 12 entrys (the functions are built with macros).
// This makes kind of sense, since using more than 12 elements in a tuple might be bad design, but using 12 pharsers in a row doesn't seem THAT unplausible.
// trait to use tuples of functions in pharsers (for alt and seq)
// trait Parsable<'a, T> {
//     fn alt(self, to_parse: &'a str) -> ParseResult<'a, T>;
//     // the accumulator gets passed by the user facing function, to insert the results.
//     //fn seq(self, to_parse: &'a str, accumulator: Vec<T>) -> ParseResult<'a, Vec<T>>;
//     // returns the length of the tuple
//     //fn len(self) -> isize;
// }
// // implementation for alt on a single element of a tuple (for this simple function, it is a bit of an overkill, but it makes sense for seq)
// fn singleton_alt<'a, T, P>(to_parse: &'a str, pharser: P) -> ParseResult<'a, T>
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> ParseResult<'a, T>,
// {
//     pharser(to_parse)
// }
// fn singelton_seq<'a, 'b, T, P>(to_parse: &'a str, pharser: P, mut accumulator: Vec<T>) -> ParseResult<'a, Vec<T>>
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> ParseResult<'a, T>,
// {
//     let result : T;
//     let to_parse_tail: &str;
//     (result, to_parse_tail) = pharser(to_parse)?;
//     accumulator.push(result);
//     Ok((accumulator, to_parse_tail))
// }

// // implement the trait for singleton tuple of pharsers
// impl<'a, T, P> Parsable<'a, T> for (P,)
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> ParseResult<'a, T>,
// {
//     // base case
//     fn alt(self, to_parse: &'a str) -> ParseResult<'a, T> {
//         singleton_alt(to_parse, self.0) // call the function on the last tuple entry
//     }
//     // fn seq(self, to_parse: &'a str, accumulator: Vec<T>) -> ParseResult<'a, Vec<T>> {
//     //     // a little bit weird that this works, because the passed accumulator isn't necessary mutable? -> but it gets moved into here, so I guess I've got full control...
//     //     singelton_seq(to_parse, self.0, accumulator)
//     // }
// }
// // implement the trait for all other tuples
// impl<'a, T, P, Rest> Parsable<'a, T> for (P, Rest)
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> ParseResult<'a, T>,
//     Rest: Parsable<'a, T>,
// {
//     // recursive case
//     fn alt(self, to_parse: &'a str) -> ParseResult<'a, T> {
//         match singleton_alt(to_parse, self.0) { // apply first pharser
//             ok @ Ok(_) => ok, // More elegant form of Ok(a) => Ok(a), because we don't repack a.
//             Err(_) => self.1.alt(to_parse) // apply the next pharser
//         }
//     }
//     // fn seq(self, to_parse: &'a str, accumulator: Vec<T>) -> ParseResult<'a, Vec<T>> {
//     //     // let result : T;
//     //     // let to_parse_tail: &str;
//     //     // (result, to_parse_tail) = (self.0)(to_parse)?;
//     //     // accumulator.push(result);
//     //     let (accumulator, to_parse_tail) = singelton_seq(to_parse, self.0, accumulator)?;
//     //     // also do the rest of the tuple
//     //     Ok(self.1.seq(to_parse_tail, accumulator)?)
//     // }
// }
// // implement as a function
// fn alt<'a, T, Parsers>(to_parse: &'a str, parsers: Parsers) -> ParseResult<'a, T> 
// where
//     Parsers: Parsable<'a, T>,   
// {
//     parsers.alt(to_parse)
// }
// fn seq<'a, 'b, T, Parser>(to_parse: &'a str, parsers: Parser) -> ParseResult<'a, Vec<T>>
// where
//     Parser: Parsable<'a, 'b, T>
// {
//     let accumulator: Vec<T> = Vec::with_capacity(10);
//     let (filled_accumulator, to_parse_tail)  = parsers.seq(to_parse, accumulator)?;
//     Ok((filled_accumulator, to_parse_tail))
//     //Err("not implemented yet")
// }

// another attempt at infinite tuple traits
trait Countable {
    fn my_count(&self) -> i32;
}
// base case
// impl<P> Countable for (P,) {
//     fn my_count(self) -> i32 {
//         1
//     }
// }
// // recursive case
// impl<P, Rest> Countable for (P, Rest)
// where Rest: Countable
// {
//     fn my_count(self) -> i32 {
//         1 + (self.1).my_count()
//     }
// }
// implement for list?
// it works!!! -> But lists are homogenous, so this doesn't help at all.

impl<P> Countable for [P]
{
    fn my_count(&self) -> i32 {
        match self {
            [_]  => 1,
            _ => 1 + (self[1..]).my_count()
        }
        
    }
}

/// returns the result of the first succeding pharser
pub fn alt<'a, T>(to_parse: &'a str, pharsers: Vec<&dyn Fn(&'a str) -> ParseResult<'a, T>>) -> ParseResult<'a, T>
{
    let pharser = &pharsers[0];
    match pharser(to_parse) {
        Ok(a) => Ok(a),
        Err(_) => {
            if pharsers.len() > 1 {
                alt(to_parse, pharsers[1..].to_vec())
            } else {
                Err("none of the provided parsers matched".to_string())
            }
        },
    }
}

//struct PharserSequence {
    // Maybe seq can be implemented as a iterator (don't know if that would give any benefit to be honest, but it would be cool)
    // https://doc.rust-lang.org/std/iter/index.html#implementing-iterator
//}

// maybe it is possible to implement this with a macro?
/// takes the output of the first pharser as input for the next
// actually it might be a good thing to not let the compiler generate a new seq function for each pharser that the program passes into it
pub fn seq<'a, 'b, T>(to_parse: &'a str, pharsers: Vec<&dyn Fn(&'a str) -> ParseResult<'a, T>>) -> ParseResult<'a, Vec<T>>
{
    let mut results: Vec<T> = Vec::with_capacity(pharsers.len());
    let mut remaining: &str = to_parse;
    for pharser in pharsers {
        let result : T;
        (result, remaining) = pharser(remaining)?;
        results.push(result);
    }
    Ok((results, remaining))
}
/// removes whitespaces at the beginning of the input.
/// whitespaces are determined by rusts is_whitespace method on characters.
/// This pharser also succeeds if there is no space.
/// returns the removed whitespaces.
pub fn space<'a>(to_parse: &'a str) ->ParseResult<'a, String> {
    many(to_parse, |input| item_satisfies(input, |x| x.is_whitespace()))
}
// now it starts to get language specific! //////////////////////////////////////////
// The following pharsers care about space before and after them.

/// Pharses natural numbers up to 2^63 - 1 (that's the max i64)
pub fn nat<'a>(to_parse: &'a str) -> ParseResult<'a, String> {
    match some(to_parse, digit) {
        ok @ Ok(_) => ok,
        Err(_) => Err(format!("expected a number, found {}", item(to_parse)?.0)), // this line will propagate the end of file error message, if item fails
    }
}


/// Pharses identifiers: string of characters, terminatet by any non alphanumeric
pub fn sym<'a>(to_parse: &'a str) -> ParseResult<'a, String> {
    let pharser_result = {
        let (a, to_parse) = some(to_parse, alphabetic)?;
        let (b, to_parse) = many(to_parse, alphanumeric)?;
        Ok((format!("{a}{b}"), to_parse))
    };
    match pharser_result {
        ok @ Ok(_) => ok,
        Err(_) => Err("expected a identifier".to_string()),
    }
}

pub fn operator<'a>(to_parse: &'a str) -> ParseResult<'a, String> {
    let pharser_result = {
        let (a, to_parse) = some(to_parse, valid_operator)?;
        Ok((a, to_parse))
    };
    match pharser_result {
        ok @ Ok(_) => ok,
        Err(_) => Err("expected non alphanumeric.".to_string()),
    }
}

/// applies the given parser to some token surrounded by whitespace
/// in other words in this string: "  abc   hello" it would check if "abc" gives a result from the parser.
/// If that parser would suceed (as for example the alphabetic pharser would) it returns "hello" as the . 
pub fn token<'a, P, T>(to_parse: &'a str, pharser: P) -> ParseResult<'a, String>
where P: Fn(&'a str) -> ParseResult<'a, T>, T: ToString
{
    let (_, to_parse) = space(to_parse)?; // space parser can't fail.
    let (my_token, to_parse) = some(to_parse, pharser)?;
    let (_, to_parse) = space(to_parse)?; // space parser can't fail
    Ok((my_token, to_parse))
}

/// takes a parser, whose sucess is optional.
/// On sucess, the returned to_parse string will be returned
/// otherwise the provided to_parse string gets returned unchanged.
/// If the parser suceeds, its returned value will be applied to S
/// else the this function returns the default argument
/// # Examples
/// Check if the next character in to_parse is a minussign,
/// The following value (which is parsed later) is negative.
/// ```
/// to_parse = "-25"
/// let (is_negative, to_parse) = optional(to_parse, |x|char(x, '-'), |x, _|Ok((true, x)), false)?;
/// assert_eq!(is_negative, true);
/// ````
pub fn optional<'a, P, S, T, R>(to_parse: &'a str, parser: P, sucess_fn: S, default: R) -> ParseResult<'a, R> 
where P: Fn(&'a str) -> ParseResult<'a, T>, S: Fn(&'a str, T) -> ParseResult<'a, R>
{
    match parser(to_parse) {
        Ok((parse_result, to_parse)) => {
            (sucess_fn(to_parse, parse_result))
        },
        Err(_) => Ok((default, to_parse)),
    }
}

/// maps the result of the given parser to the given function. Fails if the parser fails.
pub fn map<'a, P, S, T, R>(to_parse: &'a str, parser: P, sucess_fn: S) -> ParseResult<'a, R>
where P: Fn(&'a str) -> ParseResult<'a, T>, S: Fn(T) -> R
{
    let (res, to_parse) = parser(to_parse)?;
    Ok((sucess_fn(res),
    to_parse))
}

/// uses content_parser on the input until whatever closing_parser matches, if to_parse starts with something which opeining_parser matches.
/// Used to parse content withing brackets.
pub fn within<'a, O, T, C, Po, P, Pc>(to_parse: &'a str, opening_parser: Po, content_parser: P, closing_parser: Pc) -> ParseResult<'a, T>
where
Po: Fn(&'a str) -> ParseResult<'a, O>,
P: Fn(&'a str) -> ParseResult<'a, T>,
Pc: Fn(&'a str) -> ParseResult<'a, C>,
{
    let (_, to_parse) = opening_parser(to_parse)?; // when this fails, the whole parser fails
    let (content, to_parse) = content_parser(to_parse)?;
    let (_, to_parse) = closing_parser(to_parse)?;
    Ok((content, to_parse))
}

fn internal_testing() {
    match nat("2147483647") {
        Ok((num, tail)) => println!("we got the number: {} with pharse tail: {}", num, tail),
        Err(msg) => println!("{}",msg),
    }
    match nat("2147483648") {
        Ok((num, tail)) => println!("we got the number: {} with pharse tail: {}", num, tail),
        Err(msg) => println!("{}",msg),
    }
    let (first_char, _) = item(&"Hello, world!").expect("hell is melting");
    println!("first pharsed char: {}",first_char);
    let (first_char, _) = item(&"🐦 <- this is a regular bird").expect("");
    let (second_char, _) = item(&"🐦‍⬛ <- this is a black bird ").expect("");
    println!("first char: {}, second char: {}", first_char, second_char);
    let (blackbird_vec, _) = seq("🐦‍⬛???",vec![&item, &item, &item, &item]).expect("yeah, that will work...");
    //let (blackbird_vec, _) = seq("🐦‍⬛???",(item, item, item, item)).expect("yeah, that will work...");
    let blackbird:String = blackbird_vec.iter().collect();
    println!("Debug blackbird: {:?}",blackbird);
    println!("blackbird: {}", blackbird);
    println!("actual blackbird: {}", "🐦‍⬛");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_item(){
        assert_eq!(item(&"hallo"), Ok(('h', "allo")));
        assert_eq!(item(&"🦀hallo"), Ok(('🦀', "hallo")));
    }

    #[test]
    fn test_item_satisfies() {
        let input = "ab";
        let predicate = |x: char| x.is_ascii_alphabetic();
        let result = item_satisfies(input,  predicate);
        assert_eq!(Ok(('a', "b")), result);
    }
    #[test]
    fn test_alphabetic() {
        let result = alphabetic("abcde");
        assert_eq!(Ok(('a',"bcde")), result);
    }

    #[test]
    fn test_some_success() {
        let input = "hello15ducks";
        let result = some(input, alphabetic);
        assert_eq!(Ok(("hello".to_string(), "15ducks")), result)
    }
    #[test]
    /// This test shall fail in the future, because I want to change the error message to be even more specific
    /// (position of the failure)
    fn test_some_failure() {
        let input = "15ducks";
        let result = some(input, alphabetic);
        assert_eq!(Err("character '1' doesn't fulfill predicate".to_string()), result)
    }
    #[test]
    fn test_alt() {
        let result = alt("123", vec![&alphabetic, &item]);
        //let result = alt("123", (alphabetic, alphabetic));
        assert_eq!(Ok(('1', "23")), result)
    }

    #[test]
    fn test_seq() {
        let input = "abcdefg";
        let result = seq(input, vec![&item, &item, &item]);
        assert_eq!(Ok((vec!['a', 'b', 'c'], "defg")), result);
    }
}