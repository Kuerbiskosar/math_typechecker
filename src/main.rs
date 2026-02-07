mod numbersystem;
mod term;
mod pharsers;
mod language_parsers;

use pharsers::Parsable;
use language_parsers::parse_file;

use crate::term::Environment;

fn main() {
    //let file_path = std::env::args().nth(1).expect("no path given");
    let file_path = "test_comments.tc";
    println!("File path: {:?}", file_path);
    let contents = std::fs::read_to_string(file_path)
        .expect("Should have been able to read the file");
    println!("File contents:\n---------------\n{}\n---------------", contents);
    let mut env_tracker = Environment::new();

    let to_parse = Parsable::with_string(&contents);
    let (_, parsed) = parse_file(to_parse, &mut env_tracker);
    let parse_errors = parsed.get_info().errors;

    if parse_errors.len() > 0 {
        println!("
        ---------------------------------------
        +       PARSE ERROR OCCURRED!!!       +
        ---------------------------------------
        ");
        for err in parse_errors {
            println!("{} at {}", err.msg, err.pos.to_text_pos(&contents))
        }
        println!("---------------------------------------")
    }
    env_tracker.evaluate_and_print_all_variables();
    env_tracker.print_all_comment_locations(&contents);
}