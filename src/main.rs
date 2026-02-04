mod numbersystem;
mod term;
mod pharsers;
mod language_parsers;

use std::collections::HashMap;
use pharsers::Parsable;
use language_parsers::parse_assignment;

fn main() {
    //let file_path = std::env::args().nth(1).expect("no path given");
    let file_path = "testfile.tc";
    println!("pattern: {:?}", file_path);
    let contents = std::fs::read_to_string(file_path)
        .expect("Should have been able to read the file");
    println!("{}", contents);
    let mut env_tracker = HashMap::default();
    for line in contents.lines() {
        if line.chars().count() == 0 {continue};
        (env_tracker, _) = parse_assignment(Parsable::with_string(line), env_tracker).expect("failed to parse");
    }

    // pretty print the environment
    for (key, value) in &env_tracker {
        println!("variable name: {key}, \n\tvalue: {}", value.content);
        let result = value.evaluate(&env_tracker);
        match result {
            Ok(num) => println!("\tevaluates to: {num}"),
            Err(msg) => println!("evaluation failed with error: {msg:?}"),
        }
    }
}