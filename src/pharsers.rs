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
//pub type ParseResult<'a,T> = Result<(T, &'a str), String>; // error messages must be strings, because they contain information which is not known at compile time (such as on which line the error ocurred)
pub type ParseResult<'a,T> = Result<(T, Parsable<'a>), (Parsable<'a>, Info)>;
//type Pharser2<'a, T> = dyn Fn(&str) -> ParseResult<'a, T>;
//type Pharser = &str -> Result<(char,int),&str>;


// Struct to keep track of parse errors and warnings
// keeps a reference to part of the parse input string.
// the information collector keeps track of warnings collected in a previous
// parse step.
#[derive(Clone, Debug, PartialEq)]
pub struct Parsable<'a> {
    content: &'a str,
    pub span: Span,
    information: InformationCollector
}

#[derive(Copy, Clone, Debug)]
pub struct ShallowParser<'a> {
    content: &'a str,
    pub span: Span,
    info_len: usize,
    warning_len: usize,
    error_len: usize,
}
impl<'a> ShallowParser<'a> {
    pub fn new(parsable: &Parsable<'a>) -> ShallowParser<'a>{
        ShallowParser {
            content: parsable.content,
            span: parsable.span,
            info_len: parsable.information.infos.len(),
            warning_len: parsable.information.warnings.len(),
            error_len: parsable.information.errors.len()
        }
    }
}

impl<'a> Parsable<'a> {
    /// restores the parsable to its source.
    /// This function must be used when returning the parser contents in an parser error.
    pub fn restore(mut self, shallow_parser: ShallowParser<'a>) -> Self {
        self.content = shallow_parser.content;
        self.span = shallow_parser.span;
        self.information.infos.truncate(shallow_parser.info_len);
        self.information.warnings.truncate(shallow_parser.warning_len);
        self.information.errors.truncate(shallow_parser.error_len);
        self
    }

    pub fn with_string(to_parse: &'a str) -> Parsable<'a>{
        Parsable {
            content: to_parse,
            span: Span { start: 0, end: to_parse.chars().count()},
            // Removal of entries into this field may only be done through the ShallowParser
            // The Idea is to restore a previous parsable state through the length of the vector
            // This has to be done, if a parser suceeds, but a subsequent parser step fails.
            // This prevents unnecessary cloning of the information vector.
            information: InformationCollector { infos: Vec::new(), warnings: Vec::new(), errors: Vec::new() }
        }
    }
    /// creates a string with a span start offset from zero.
    /// This is useful for constructing expected output spans.
    pub fn with_str_offset(to_parse: &'a str, offset: usize) -> Parsable<'a> {
        Parsable {
            content: to_parse,
            span: Span {start: offset, end: to_parse.chars().count()+offset},
            information: InformationCollector { infos: Vec::new(), warnings: Vec::new(), errors: Vec::new() }
        }
    }
    pub fn add_info(mut self, info: Info) -> Parsable<'a> {
        self.information.infos.push(info);
        self
    }
    pub fn add_warning(mut self, info: Info) -> Parsable<'a> {
        self.information.infos.push(info);
        self
    }
    pub fn add_error(mut self, info: Info) -> Parsable<'a> {
        self.information.infos.push(info);
        self
    }

    /// This function returns the next char in line, without changing the parser.
    /// This should be used for error messages.
    pub fn get_next_char(&self) -> String {
        match self.content.chars().nth(0) {
            Some(c) => c.to_string(),
            None => "<End Of Line>".to_string(),
        }
    }
    // Note: consider implementing get_next_token for error message purposes.
}

#[derive(Clone, Debug, PartialEq)]
pub struct InformationCollector {
    infos: Vec<Info>,
    warnings: Vec<Info>,
    errors: Vec<Info>
}
// Implements the three commonly used warning levels: info, warning and error.
#[derive(Clone, Debug, PartialEq)]
pub struct Info {
    pub msg: String,
    pub pos: Span,
}


// struct to track position of errors in the input string
// end exclusive. start and end are the same for a span of ZERO characters (at the end of parsing).
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize
}
// struct to represent span in a human readable format
struct TextPos {
    start_line: usize,
    start_pos_in_line: usize,
    end_line: usize,
    end_pos_in_line: usize
}

/// returns (line number, position in line) beginning of the given string
fn string_position(slice:&str, full:&str) -> TextPos {
    let x = &slice;
    todo!()
}

// gets one character from the string. basic building block for further pharsers
pub fn item<'a>(mut to_parse: Parsable<'a>) -> ParseResult<'a, char> {
    // condiser pharsing whole grapheme clusters, to interpret symbols build with stopchars and their "hardcoded" unicode equivalent the same
    fn strip_first_char(to_strip: &str) -> &str {
        let mut chars = to_strip.chars();
        chars.next();
        chars.as_str()
    }
    match to_parse.content.chars().nth(0) {
        Some(character) => {
            to_parse.content = strip_first_char(to_parse.content);
            to_parse.span =  Span { start: to_parse.span.start +1, end: to_parse.span.end};
            // to_parse.information left unchanged.
            // let parsable = Parsable {
            //     content: strip_first_char(to_parse.content),
            //     span: Span { start: to_parse.span.start -1, end: to_parse.span.end},
            //     information: to_parse.information,
            // };
            Ok((character, to_parse))
        },
        None => {
            // Note: I add to_parse.span.start at the end of the span, because maybe there is a possibility that chars.next() stops iteration
            // even thought the string is not at the end... (or maybe the to_parse.span.end was set wrong, which is much more likely)
            let info = Info { msg: "unexpected end of input".to_string(), pos: Span { start: to_parse.span.start, end: to_parse.span.start }};
            Err((to_parse, info))
        },
    }
}
/// succeeds with the first character, if the character fulfills the predicate
fn item_satisfies<'a, Predicate>(to_parse: Parsable<'a>, predicate: Predicate) -> ParseResult<'a, char> 
where
    Predicate: Fn(char) -> bool
{
    let original_parsable = ShallowParser::new(&to_parse);
    let (token, remaining) = item(to_parse)?;
    if predicate(token) {
        Ok((token, remaining))
    } else {
        let to_parse = remaining.restore(original_parsable);
        let info = Info {
            msg: format!("character '{}' doesn't fulfill predicate", token),
            // end = start, because only one character can be affected through the item parser
            pos: Span { start: to_parse.span.start, end: to_parse.span.start }
        };
        Err((to_parse, info))
    }
}

// single character pharsers

fn alphabetic<'a>(to_parse:Parsable<'a> ) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x: char| x.is_alphabetic())
}
fn digit<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_digit(10)) // consider adding pharsers for other common bases
}
fn alphanumeric<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_alphanumeric())
}
fn valid_operator<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x: char|   !x.is_alphanumeric() &&
                                                    !x.is_whitespace() &&
                                                    !(x == '(') && !(x == ')'))
}

fn upper<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_uppercase())
}
fn lower<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x|x.is_lowercase())
}
pub fn char<'a>(to_parse: Parsable<'a>, char_to_match: char) -> ParseResult<'a, char> {
    item_satisfies(to_parse, |x| x == char_to_match)
}

// applies the pharser at least once
pub fn some<'a, Parser, S>(to_parse: Parsable<'a>, parser: Parser) -> ParseResult<'a, String> 
where
   Parser: Fn(Parsable<'a>) -> ParseResult<'a, S>,
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
/// If this parser fails, it returns an empty string
pub fn many<'a, Parser, S>(to_parse: Parsable<'a>, parser: Parser) -> ParseResult<'a, String>
where
   Parser: Fn(Parsable<'a>) -> ParseResult<'a, S>,
   S: ToString
{
    match parser(to_parse) {
        Ok((a, to_parse_tail)) => {
            match some(to_parse_tail, parser) {
                Ok((string, pharse_tail)) => Ok((format!("{}{}", a.to_string(), string), pharse_tail)),
                Err((parsable, _)) => Ok((a.to_string(), parsable)), // return with empty string
            }
        },
        Err((parsable, _)) => Ok(("".to_string(), parsable)),
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
pub fn alt<'a, T>(to_parse: Parsable<'a>, pharsers: Vec<&dyn Fn(Parsable<'a>) -> ParseResult<'a, T>>) -> ParseResult<'a, T>
{
    let pharser = &pharsers[0];
    match pharser(to_parse) {
        Ok(a) => Ok(a),
        Err((to_parse, info)) => {
            if pharsers.len() > 1 {
                alt(to_parse, pharsers[1..].to_vec())
            } else {
                let info = Info {msg: "none of the provided parsers matched".to_string(), pos: info.pos};
                Err((to_parse, info))
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
pub fn seq<'a, 'b, T>(to_parse: Parsable<'a>, pharsers: Vec<&dyn Fn(Parsable<'a>) -> ParseResult<'a, T>>) -> ParseResult<'a, Vec<T>>
{
    let mut results: Vec<T> = Vec::with_capacity(pharsers.len());
    let mut remaining= to_parse;
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
pub fn space<'a>(to_parse: Parsable<'a>) ->ParseResult<'a, String> {
    many(to_parse, |input| item_satisfies(input, |x| x.is_whitespace()))
}
// now it starts to get language specific! //////////////////////////////////////////
// The following pharsers care about space before and after them.

/// Pharses natural numbers up to 2^63 - 1 (that's the max i64)
pub fn nat<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, String> {
    match some(to_parse, digit) {
        ok @ Ok(_) => ok,
        Err((parsable, info)) => {
            let next_item = parsable.get_next_char();
            let info = Info {msg: format!("expected a number, found {}", next_item), pos: info.pos};
            Err((parsable, info))
        }
    }
}


/// Pharses identifiers: string of characters, terminatet by any non alphanumeric
pub fn sym<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, String> {
    let pharser_result = {
        let (a, to_parse) = some(to_parse, alphabetic)?;
        let (b, to_parse) = many(to_parse, alphanumeric)?;
        Ok((format!("{a}{b}"), to_parse))
    };
    match pharser_result {
        ok @ Ok(_) => ok,
        
        Err((parsable, info)) => {
            let info = Info {msg: "expected a identifier (something which starts with a alphabetic character)".to_string(), pos: info.pos};
            Err((parsable, info))
        },
    }
}

pub fn operator<'a>(to_parse: Parsable<'a>) -> ParseResult<'a, String> {
    let pharser_result = {
        let (a, to_parse) = some(to_parse, valid_operator)?;
        Ok((a, to_parse))
    };
    match pharser_result {
        ok @ Ok(_) => ok,
        Err((parsable, info)) => {
            let info = Info { msg: "expected non alphanumeric.".to_string(), pos: info.pos };
            Err((parsable, info))
        },
    }
}

/// applies the given parser to some token surrounded by whitespace
/// in other words in this string: "  abc   hello" it would check if "abc" gives a result from the parser.
/// If that parser would suceed (as for example the alphabetic pharser would) it returns "hello" as the . 
pub fn token<'a, P, T>(to_parse: Parsable<'a>, pharser: P) -> ParseResult<'a, String>
where P: Fn(Parsable<'a>) -> ParseResult<'a, T>, T: ToString
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
/// let to_parse = Parsable::with_string("-25");
/// let (is_negative, to_parse) = optional(to_parse, |x|char(x, '-'), |x, _|Ok((true, x)), false)?;
/// assert_eq!(is_negative, true);
/// ````
pub fn optional<'a, P, S, T, R>(to_parse: Parsable<'a>, parser: P, sucess_fn: S, default: R) -> ParseResult<'a, R> 
where P: Fn(Parsable<'a>) -> ParseResult<'a, T>, S: Fn(Parsable<'a>, T) -> ParseResult<'a, R>
{
    match parser(to_parse) {
        Ok((parse_result, to_parse)) => {
            (sucess_fn(to_parse, parse_result))
        },
        Err((parsable, _)) => Ok((default, parsable)),
    }
}

/// maps the result of the given parser to the given function. Fails if the parser fails.
pub fn map<'a, P, S, T, R>(to_parse: Parsable<'a>, parser: P, sucess_fn: S) -> ParseResult<'a, R>
where P: Fn(Parsable<'a>) -> ParseResult<'a, T>, S: Fn(T) -> R
{
    let (res, to_parse) = parser(to_parse)?;
    Ok((sucess_fn(res),
    to_parse))
}

/// uses content_parser on the input until whatever closing_parser matches, if to_parse starts with something which opeining_parser matches.
/// Used to parse content withing brackets.
pub fn within<'a, O, T, C, Po, P, Pc>(to_parse: Parsable<'a>, opening_parser: Po, content_parser: P, closing_parser: Pc) -> ParseResult<'a, T>
where
Po: Fn(Parsable<'a>) -> ParseResult<'a, O>,
P: Fn(Parsable<'a>) -> ParseResult<'a, T>,
Pc: Fn(Parsable<'a>) -> ParseResult<'a, C>,
{
    let (_, to_parse) = opening_parser(to_parse)?; // when this fails, the whole parser fails
    let (content, to_parse) = content_parser(to_parse)?;
    let (_, to_parse) = closing_parser(to_parse)?;
    Ok((content, to_parse))
}

fn internal_testing() {
    match nat(Parsable::with_string("2147483647")) {
        Ok((num, tail)) => println!("we got the number: {} with pharse tail: {}", num, tail.content),
        Err(msg) => println!("{}",msg.1.msg),
    }
    match nat(Parsable::with_string("2147483648")) {
        Ok((num, tail)) => println!("we got the number: {} with pharse tail: {}", num, tail.content),
        Err(msg) => println!("{}",msg.1.msg),
    }
    let (first_char, _) = item(Parsable::with_string("Hello, world!")).expect("hell is melting");
    println!("first pharsed char: {}",first_char);
    let (first_char, _) = item(Parsable::with_string("🐦 <- this is a regular bird")).expect("");
    let (second_char, _) = item(Parsable::with_string("🐦‍⬛ <- this is a black bird ")).expect("");
    println!("first char: {}, second char: {}", first_char, second_char);
    let (blackbird_vec, _) = seq(Parsable::with_string("🐦‍⬛???"),vec![&item, &item, &item, &item]).expect("yeah, that will work...");
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
        assert_eq!(item(Parsable::with_string("hallo")), Ok(('h', Parsable::with_str_offset("allo", 1))));
        assert_eq!(item(Parsable::with_string("🦀hallo")), Ok(('🦀', Parsable::with_str_offset("hallo", 1))));
    }

    #[test]
    fn test_item_satisfies() {
        let input = Parsable::with_string("ab");
        let predicate = |x: char| x.is_ascii_alphabetic();
        let result = item_satisfies(input,  predicate);
        assert_eq!(Ok(('a', Parsable::with_str_offset("b", 1))), result);
    }
    #[test]
    fn test_alphabetic() {
        let input = Parsable::with_string("abcde");
        let result = alphabetic(input);
        assert_eq!(Ok(('a',Parsable::with_str_offset("bcde", 1))), result);
    }

    #[test]
    fn test_some_success() {
        let input = Parsable::with_string("hello15ducks");
        let result = some(input, alphabetic);
        assert_eq!(Ok(("hello".to_string(), Parsable::with_str_offset("15ducks", 5))), result)
    }
    #[test]
    /// This test shall fail in the future, because I want to change the error message to be even more specific
    /// (position of the failure)
    fn test_some_failure() {
        let input = Parsable::with_string("15ducks");
        let result = some(input, alphabetic);
        let info = Info { msg: "character '1' doesn't fulfill predicate".to_string(), pos: Span { start: 0, end: 0 } };
        assert_eq!(Err((Parsable::with_string("15ducks"), info)), result)
    }
    #[test]
    fn test_alt() {
        let result = alt(Parsable::with_string("123"), vec![&alphabetic, &item]);
        //let result = alt("123", (alphabetic, alphabetic));
        assert_eq!(Ok(('1', Parsable::with_str_offset("23", 1))), result)
    }

    #[test]
    fn test_seq() {
        let input = Parsable::with_string("abcdefg");
        let result = seq(input, vec![&item, &item, &item]);
        assert_eq!(Ok((vec!['a', 'b', 'c'], Parsable::with_str_offset("defg", 3))), result);
    }
}