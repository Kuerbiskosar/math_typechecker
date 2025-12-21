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
type PharseResult<'a,T> = Result<(T, &'a str), String>; // error messages must be strings, because they contain information which is not known at compile time (such as on which line the error ocurred)
//type Pharser2<'a, T> = dyn Fn(&str) -> PharseResult<'a, T>;
//type Pharser = &str -> Result<(char,int),&str>;
// gets one character from the string. basic building block for further pharsers
fn item<'a>(to_pharse: &'a str) -> PharseResult<'a, char> {
    // condiser pharsing whole grapheme clusters, to interpret symbols build with stopchars and their "hardcoded" unicode equivalent the same
    fn strip_first_char(to_strip: &str) -> &str {
        let mut chars = to_strip.chars();
        chars.next();
        chars.as_str()
    }
    match to_pharse.chars().nth(0) {
        Some(character) => Ok((character, strip_first_char(to_pharse))),
        None => Err("End of input".to_string()),
    }
}
/// succeeds with the first character, if the character fulfills the predicate
fn item_satisfies<'a, Predicate>(to_pharse: &'a str, predicate: Predicate) -> PharseResult<'a, char> 
where
    Predicate: Fn(char) -> bool
{
    let (token, remaining) = item(&to_pharse)?;
    if predicate(token) {
        Ok((token, remaining))
    } else {
        Err("character doesn't fulfill predicate".to_string())
    }
}

// single character pharsers

fn alphabetic<'a>(to_pharse: &'a str) -> PharseResult<'a, char> {
    item_satisfies(to_pharse, |x: char| x.is_alphabetic())
}
fn digit<'a>(to_pharse: &'a str) -> PharseResult<'a, char> {
    item_satisfies(to_pharse, |x|x.is_digit(10)) // consider adding pharsers for other common bases
}
fn alphanumeric<'a>(to_pharse: &'a str) -> PharseResult<'a, char> {
    item_satisfies(to_pharse, |x|x.is_alphanumeric()) // consider adding pharsers for other common bases
}

fn upper<'a>(to_pharse: &'a str) -> PharseResult<'a, char> {
    item_satisfies(to_pharse, |x|x.is_uppercase()) // consider adding pharsers for other common bases
}
fn lower<'a>(to_pharse: &'a str) -> PharseResult<'a, char> {
    item_satisfies(to_pharse, |x|x.is_lowercase()) // consider adding pharsers for other common bases
}
fn char<'a>(to_pharse: &'a str, char_to_match: char) -> PharseResult<'a, char> {
    item_satisfies(to_pharse, |x| x == char_to_match) // consider adding pharsers for other common bases
}

// applies the pharser at least once
fn some<'a, Parser, S>(to_pharse: &'a str, parser: Parser) -> PharseResult<'a, String> 
where
   Parser: Fn(&'a str) -> PharseResult<'a, S>,
   S: ToString
   //Parser: Fn(&'a str) -> Result<(char, &'a str), &str>
{
    match parser(to_pharse) {
        Ok((a, to_pharse_tail)) => {
            match many(to_pharse_tail, parser) {
                Ok((string, pharse_tail)) => Ok((format!("{}{}", a.to_string(), string), pharse_tail)),
                err @ Err(_) => err,
            }
        },
        Err(message) => Err(message)
    }
}
/// applies the pharser until it fails, returning the result as a string
/// The result of the pharser must be convertible to a string
fn many<'a, Parser, S>(to_pharse: &'a str, parser: Parser) -> PharseResult<'a, String>
where
   Parser: Fn(&'a str) -> PharseResult<'a, S>,
   S: ToString
{
    match parser(to_pharse) {
        Ok((a, to_pharse_tail)) => {
            match some(to_pharse_tail, parser) {
                Ok((string, pharse_tail)) => Ok((format!("{}{}", a.to_string(), string), pharse_tail)),
                Err(_) => Ok((a.to_string(), to_pharse_tail)), // return with empty string
            }
        },
        Err(_) => Ok(("".to_string(), to_pharse)),
    }
}

// this doesn't work. Once again, I was a fool to follow the advice of a large language model.
// usually functions which take tuples of "arbitrary" length are limited to 12 entrys (the functions are built with macros).
// This makes kind of sense, since using more than 12 elements in a tuple might be bad design, but using 12 pharsers in a row doesn't seem THAT unplausible.
// trait to use tuples of functions in pharsers (for alt and seq)
// trait Parsable<'a, T> {
//     fn alt(self, to_pharse: &'a str) -> PharseResult<'a, T>;
//     // the accumulator gets passed by the user facing function, to insert the results.
//     //fn seq(self, to_pharse: &'a str, accumulator: Vec<T>) -> PharseResult<'a, Vec<T>>;
//     // returns the length of the tuple
//     //fn len(self) -> isize;
// }
// // implementation for alt on a single element of a tuple (for this simple function, it is a bit of an overkill, but it makes sense for seq)
// fn singleton_alt<'a, T, P>(to_pharse: &'a str, pharser: P) -> PharseResult<'a, T>
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> PharseResult<'a, T>,
// {
//     pharser(to_pharse)
// }
// fn singelton_seq<'a, 'b, T, P>(to_pharse: &'a str, pharser: P, mut accumulator: Vec<T>) -> PharseResult<'a, Vec<T>>
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> PharseResult<'a, T>,
// {
//     let result : T;
//     let to_pharse_tail: &str;
//     (result, to_pharse_tail) = pharser(to_pharse)?;
//     accumulator.push(result);
//     Ok((accumulator, to_pharse_tail))
// }

// // implement the trait for singleton tuple of pharsers
// impl<'a, T, P> Parsable<'a, T> for (P,)
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> PharseResult<'a, T>,
// {
//     // base case
//     fn alt(self, to_pharse: &'a str) -> PharseResult<'a, T> {
//         singleton_alt(to_pharse, self.0) // call the function on the last tuple entry
//     }
//     // fn seq(self, to_pharse: &'a str, accumulator: Vec<T>) -> PharseResult<'a, Vec<T>> {
//     //     // a little bit weird that this works, because the passed accumulator isn't necessary mutable? -> but it gets moved into here, so I guess I've got full control...
//     //     singelton_seq(to_pharse, self.0, accumulator)
//     // }
// }
// // implement the trait for all other tuples
// impl<'a, T, P, Rest> Parsable<'a, T> for (P, Rest)
// where // P is a pharser (function that takes a reference to a string and outputs a pharser result)
//     P: Fn(&'a str) -> PharseResult<'a, T>,
//     Rest: Parsable<'a, T>,
// {
//     // recursive case
//     fn alt(self, to_pharse: &'a str) -> PharseResult<'a, T> {
//         match singleton_alt(to_pharse, self.0) { // apply first pharser
//             ok @ Ok(_) => ok, // More elegant form of Ok(a) => Ok(a), because we don't repack a.
//             Err(_) => self.1.alt(to_pharse) // apply the next pharser
//         }
//     }
//     // fn seq(self, to_pharse: &'a str, accumulator: Vec<T>) -> PharseResult<'a, Vec<T>> {
//     //     // let result : T;
//     //     // let to_pharse_tail: &str;
//     //     // (result, to_pharse_tail) = (self.0)(to_pharse)?;
//     //     // accumulator.push(result);
//     //     let (accumulator, to_pharse_tail) = singelton_seq(to_pharse, self.0, accumulator)?;
//     //     // also do the rest of the tuple
//     //     Ok(self.1.seq(to_pharse_tail, accumulator)?)
//     // }
// }
// // implement as a function
// fn alt<'a, T, Parsers>(to_pharse: &'a str, parsers: Parsers) -> PharseResult<'a, T> 
// where
//     Parsers: Parsable<'a, T>,   
// {
//     parsers.alt(to_pharse)
// }
// fn seq<'a, 'b, T, Parser>(to_pharse: &'a str, parsers: Parser) -> PharseResult<'a, Vec<T>>
// where
//     Parser: Parsable<'a, 'b, T>
// {
//     let accumulator: Vec<T> = Vec::with_capacity(10);
//     let (filled_accumulator, to_pharse_tail)  = parsers.seq(to_pharse, accumulator)?;
//     Ok((filled_accumulator, to_pharse_tail))
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
fn alt<'a, T>(to_pharse: &'a str, pharsers: Vec<&dyn Fn(&'a str) -> PharseResult<'a, T>>) -> PharseResult<'a, T>
{
    let pharser = &pharsers[0];
    match pharser(to_pharse) {
        Ok(a) => Ok(a),
        Err(_) => alt(to_pharse, pharsers[1..].to_vec()),
    }
}

//struct PharserSequence {
    // Maybe seq can be implemented as a iterator (don't know if that would give any benefit to be honest, but it would be cool)
    // https://doc.rust-lang.org/std/iter/index.html#implementing-iterator
//}

// maybe it is possible to implement this with a macro?
/// takes the output of the first pharser as input for the next
// actually it might be a good thing to not let the compiler generate a new seq function for each pharser that the program passes into it
fn seq<'a, 'b, T>(to_pharse: &'a str, pharsers: Vec<&dyn Fn(&'a str) -> PharseResult<'a, T>>) -> PharseResult<'a, Vec<T>>
{
    let mut results: Vec<T> = Vec::with_capacity(pharsers.len());
    let mut remaining: &str = to_pharse;
    for pharser in pharsers {
        let result : T;
        (result, remaining) = pharser(remaining)?;
        results.push(result);
    }
    Ok((results, remaining))
}
/// removes spaces at the beginning of the input
/// This pharser also succeeds if there is no space
fn space<'a>(to_pharse: &'a str) ->PharseResult<'a, String> {
    many(to_pharse, |input| item_satisfies(input, |x| x.is_whitespace()))
}
// now it starts to get language specific! //////////////////////////////////////////
// The following pharsers care about space before and after them.

/// Pharses natural numbers up to 2^31 - 1 (that's the max i32)
fn nat<'a>(to_pharse: &'a str) -> PharseResult<'a, i32> {
    match some(to_pharse, digit) {
        Ok((number_string, to_pharse_tail)) => {
            match number_string.parse::<i32>() {
                Ok(number) => Ok((number, to_pharse_tail)),
                Err(msg) => Err(format!("Failed to pharse number made of numbers (probably too big). \n The error when converting to a number was: {}", msg.to_string())),
            }
        },
        Err(_) => todo!(),
    }
}
/// Pharses identifiers: string of characters, terminatet by any non alphanumeric
fn sym<'a>(to_pharse: &'a str) -> PharseResult<'a, String> {
    let pharser_result = {
        let (a, to_pharse) = some(to_pharse, alphabetic)?;
        let (b, to_pharse) = many(to_pharse, alphanumeric)?;
        Ok((format!("{a}{b}"), to_pharse))
    };
    match pharser_result {
        ok @ Ok(_) => ok,
        Err(_) => Err("expected a identifier".to_string()),
    }
}

/// applies the given parser to some token surrounded by whitespace
/// in other words in this string: "  abc   hello" it would check if "abc" gives a result from the parser.
/// If that parser would suceed (as for example the alphabetic pharser would) it returns "hello" as the . 
fn token<'a, P, T>(to_pharse: &'a str, pharser: P) -> PharseResult<'a, String>
where P: Fn(&str) -> PharseResult<'a, T>, T: ToString
{
    let (_, to_pharse) = many(to_pharse, space).expect("The many pharser should never be able to fail. Something has gone horribly wrong.");
    let (my_token, to_pharse) = some(to_pharse, pharser)?;
    let (_, to_pharse) = many(to_pharse, space).expect("the many pharser can't fail, something has gone horribly wrong");
    Ok((my_token, to_pharse))
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
    /// This test shall fail in the future, because I want to change the error message to be more specific
    fn test_some_failure() {
        let input = "15ducks";
        let result = some(input, alphabetic);
        assert_eq!(Err("character doesn't fulfill predicate".to_string()), result)
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